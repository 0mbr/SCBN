(**
  cbv evaluator that tries to optimize his list environment by
  stacking only lambdas that are applied.
*)

type term =
  | Var of int
  | Abs of term
  | App of term * term

(** [acons f x l] apply [f] to [x] and concatenate the result to [l]. *)
let acons f x l = f x :: l

(** Shift system (in a cbv evaluator) : 

    ~ Goal : Compression of the environment when some arguments are 
      unavailable (we don't put a value that means emptiness).
    ~ Purpose : We avoid useless List searching while still using one 
      environment. Hence it's useful only when there are a lot of long
      ABS sequences that __never__ receive arguments in a term.

    ~ Description : Let depth be the size of the last abstraction sequence. Let
      partial-depth be the number of missing arguments of the last abstraction 
      sequence. example : for "(λλλλλ.[[t]]) u v", pdepth = 5 and p-depth = 3.

      Then, using the update rules defined in the function [update_shift], we 
      can use a stack to compress the environment. The way to recompute the 
      correct index of a variable (or to find out that it is not available) 
      can be seen in the function [deduce].
*)
type shift = 
{
  depth  : int; (* total depth of an abstraction sequence. *)
  pdepth : int; (* partial depth of an abstraction sequence = number of missing
                   arguments. *)
  stk    : (int * int) list
}

(** Update called at the end of an abstraction sequence that enables correct
    value deduction.
*)
let update_shift shift =
  let upd_rule (s, f) = (s+shift.pdepth, f+shift.depth) in
  let froms' = List.fold_right (acons upd_rule) shift.stk [] in 
  { pdepth = 0; depth = 0; 
    stk = if shift.pdepth > 0 then (shift.pdepth, 0) :: froms' else froms' }

(** Deduction of the index that should be used when accessing the environment
    when substituting Var k. 
    -1 means that the variable comes from a partial abstraction sequence, thus
    that it needs no binding.
*)
let deduce k stk : int =
  let rec cp rev_stk = 
    match rev_stk with
    | [] -> k
    | (s, f) :: rev_stk' -> 
      let i_env = k - s in
      if      k >= f && i_env >= f then i_env
      else if k >= f && i_env < f  then -1
      else cp rev_stk'
  in
  cp (List.rev stk)

(** Update called at the end of an abstraction sequence that prepare the 
    indices for correct value deduction. 
*)
let update_indices env pdepth =
  let rec upd cdepth t = 
    match t with
    | Var k -> if k >= cdepth then Var (k+pdepth) else Var k
    | Abs t' -> Abs (upd (cdepth+1) t')
    | App(t1, t2) -> App(upd cdepth t1, upd cdepth t2)
  in
  List.fold_right (acons (upd 0)) env []

type stack_element = 
  | Fun of term * (term list) * shift
  | Arg of term
  | Partial of int

let normalize_call_by_value t env =

  let update_state env stk shift =
    let env, stk = 
      if shift.pdepth = 0 then 
        env, stk
      else 
        update_indices env shift.pdepth, (Partial shift.pdepth) :: stk
    in
    let shift = if shift.depth = 0 then shift else update_shift shift in
    env, stk, shift
  in

  let rec step t env stk shift = 
    match t with
    | Var k       -> let env, stk, shift = update_state env stk shift in
                     step_var k env stk shift
    | Abs t       -> step_abs t env stk shift
    | App(t1, t2) -> let env, stk, shift = update_state env stk shift in
                     step t2 env (Fun(t1, env, shift) :: stk) shift

  and step_var k env stk shift = 
    let i_env = deduce k shift.stk in
    let value = if i_env = -1 then Var k else List.nth env i_env in
    match stk with 
    | [] -> value
    | Arg _ :: _ when i_env = -1 -> roll_app value stk
    | Arg _ :: _                 -> step value env stk shift
    | Fun(t, env, shift) :: stk  -> step t env (Arg value :: stk) shift
    | Partial n :: stk -> roll_abs value stk n

  and step_abs t env stk shift = 
    let shift = {shift with depth = shift.depth+1} in
    match stk with
    (* partial application case *)
    | [] | Fun _ :: _ 
    | Partial _ :: _  -> step t env stk {shift with pdepth = shift.pdepth+1}
    (* non partial case, we can load an argument in the environment *)
    | Arg t' :: stk  -> step t (t' :: env) stk shift

  (* Function to deal with the case x E1 E2 .. EN. We "roll" x into 
     applications : x -> App(x, E1) -> App(App(x, E1), E2).. *)
  and roll_app t stk = 
    match stk with
    | [] -> t
    | Arg t' :: stk' -> roll_app (App(t, t')) stk'
    | Fun(t', env', shift') :: stk -> step t' env' (Arg t :: stk) shift'
    | Partial n :: stk -> roll_abs t stk n

  (* Reconstruction of a n-partial abstraction. *)
  and roll_abs t stk n =
    if n = 0 then
      (match stk with
      | [] -> t
      | Arg _ :: _ -> assert false
      | Fun(t', env', shift') :: stk -> step t' env' (Arg t :: stk) shift'
      | Partial n :: stk -> roll_abs (Abs t) stk (n-1))
    else
      roll_abs (Abs t) stk (n-1)
  in

  step t env [] {depth = 0; pdepth = 0; stk = []}
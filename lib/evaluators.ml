(**
  SCBN Evaluators compilation.
  The main work (presentated on the paper) are Eval0, Eval1_0 and Eval2_0
*)

let list_from l k =
  let rec aux l k =
    match l, k with
    | l, 0 -> l
    | [], _ -> assert false
    | _ :: l, _ -> aux l (k-1)
  in
  aux l k

(* split (a1 :: a2 :: a3 :: a :: a4 :: a5) 3 = a1 :: a2 :: a3, a, a4 :: a5 *)
let list_split l k =
  let rec split_aux l k =
    match l, k with
    | [], _ -> assert false
    | e :: l, 0 -> [], e, l
    | e :: l, _ -> let l1, e', l2 = split_aux l (k-1) in e :: l1, e', l2
  in
  let l1, e, l2 = split_aux l k in
  l1, e, l2

(* Naive implementation from the deductive rules of the paper
  The arguments are rebuilt under the ES that were introduced in
  the environment while they were in the arg stack. *)
module Eval0 = struct
  open Term

  type structure_kind = Lambda_Struct | Struct_Frozen | Struct_NotFrozen
  type arg = term * int (* int : number of new ES above *)
  type cell = Frozen_Var | NotFrozen_Var | Arg of term ref

  let addv args v = 
    match args with 
    | [] -> [] 
    | (u, v') :: args -> (u, v+v') :: args

  let rec get_structure_kind env trm =
    match trm with
    | Var k -> (match List.nth env k with
    | Frozen_Var -> Struct_Frozen
    | NotFrozen_Var -> Struct_NotFrozen
    | Arg u -> get_structure_kind env !u)
    | Abs _ -> Lambda_Struct | App(t, _) | ES(t, _) -> get_structure_kind env t

  let rec eval trm env args pos =
    match trm with
    | Var k -> (match List.nth env k with
      | Frozen_Var -> up_structure Struct_Frozen (Var k) env args 0
      | NotFrozen_Var -> up_structure Struct_NotFrozen (Var k) env args 0
      | Arg u ->
          let u' = eval !u (list_from env (k+1)) [] pos in
          u := u';
          (match get_structure_kind env !u with
          | Lambda_Struct -> eval (shift !u (k+1)) env args pos
          | s_kind -> up_structure s_kind (Var k) env args 0))
    | Abs t -> (match args with
        | [] when pos = 0 -> Abs(eval t (Frozen_Var :: env) [] 0)
        | [] -> Abs(eval t (NotFrozen_Var :: env) [] (pos-1))
        | (u, v) :: args -> eval (ES(t, shift u v)) env (addv args v) (pos-1))
    | App(t, u) -> eval t env ((u, 0) :: args) (pos+1)
    | ES(t, u) ->
        let u = ref u in
        ES(eval t (Arg u :: env) (addv args 1) pos, !u)

  and up_structure s_kind t env args vacc = (* vacc is an accumulator *)
    match args with
    | [] -> t
    | (u, v) :: args ->
      let vacc = v + vacc in let u = shift u vacc in
      (match s_kind with
      | Struct_Frozen -> up_structure s_kind (App(t, eval u env [] 0)) env args vacc
      | Struct_NotFrozen -> up_structure s_kind (App(t, App(t, u))) env args vacc
      | Lambda_Struct -> assert false)

  let main trm = eval trm [] [] 0
end

(* Less naive implementation.

  The non consumed arguments are rebuilt under the same binders they were
   first found (Thus we don't apply shifts. All evaluators from now will be doing this. 

  Here we do this by propagating the position upward. Its value is thus of the
  number of arguments that were not consumed by lambda abstraction, or could 
  not be (due to not being directly available).

  We introduce cells of term and environments so that we don't have to
  cut lists. *)
module Eval1_0 = struct
  open Term

  type structure_kind = Lambda_Struct | Struct_Frozen | Struct_NotFrozen
  type cell = Frozen_Var | NotFrozen_Var | Arg of term ref * env
  and env = cell list  
  type arg = term * int

  let addv args v =
    match args with
    | [] -> []
    | (u, v') :: args -> 
        let v = v + v' in 
        (u, if v < 0 then 0 else v) :: args

  let rec eval t env args pos =
    match t with
    | Var k ->
        begin match List.nth env k with
        | Frozen_Var -> Var k, Struct_Frozen, pos
        | NotFrozen_Var  -> Var k, Struct_NotFrozen, pos
        | Arg(tr, env') ->
            let t, sk, _ = eval !tr env' [] pos in tr := t;
            if sk = Lambda_Struct then eval (shift t (k+1)) env args pos
            else t, sk, pos
        end
    | Abs t ->
        begin match args with
        | [] when pos = 0 -> let t, _, _ = eval t (Frozen_Var :: env) args 0 in Abs t, Lambda_Struct, 0
        | []              -> let t, _, p = eval t (NotFrozen_Var :: env) args (pos-1) in Abs t, Lambda_Struct, p + 1
        | (u, v) :: args -> eval (ES(t, shift u v)) env args (pos-1)
        end
    | App(t, u) ->
        let t, sk, p = eval t env ((u, 0) :: args) (pos+1) in
        if p = pos + 1 then
          if sk = Struct_Frozen then let u, _, _ = eval u env [] 0 in App(t, u), Struct_Frozen, p - 1
          else App(t, u), Struct_NotFrozen, p - 1
        else t, sk, p
    | ES(t, u) ->
        let tr = ref u in
        let t, sk, p = eval t (Arg(tr, env) :: env) (addv args 1) pos in
        ES(t, !tr), sk, p

  let main t = let t, _ , _= eval t [] [] 0 in t
end

(* Smarter implementation than before.
  
  We use a reduc_state record so that we don't evaluate terms that can't go
  further in their reduction with the amount of information that we bring in. 
    -> the principle is that if we don't have a lower "pos", we won't find 
    new frozen arguments so we don't run an eval. *)
module Eval1_1 = struct
  open Term

  type structure_kind = Lambda_Struct | Struct_Frozen | Struct_NotFrozen
  type cell = Frozen_Var | NotFrozen_Var | Arg of reduc_state ref * env (* ref mandatory/easier for backtracks *)
  and env = cell list 
  and arg = term * int

  and reduc_state = {t:term; sk:structure_kind; pos:int}
  let reduc_state_cons t = {t; sk=Lambda_Struct; pos=Int.max_int} (* sk is wrongly constructed but we don't care*)

  let addv args v =
    match args with
    | [] -> []
    | (u, v') :: args -> 
        let v = v + v' in 
        (u, if v < 0 then 0 else v) :: args

  let rec eval t env args pos =
    match t with
    | Var k ->
        begin match List.nth env k with
        | Frozen_Var -> Var k, Struct_Frozen, pos
        | NotFrozen_Var  -> Var k, Struct_NotFrozen, pos
        | Arg(rs, env') ->
            rs := if pos < !rs.pos then
                    let t, sk, _ = eval !rs.t env' [] pos in
                    {t; sk; pos}
                  else !rs;
            if !rs.sk = Lambda_Struct then eval (shift t (k+1)) env args pos
            else t, !rs.sk, pos
        end
    | Abs t ->
        begin match args with
        | [] when pos = 0 -> let t, _, _ = eval t (Frozen_Var :: env) args 0 in Abs t, Lambda_Struct, 0
        | []              -> let t, _, p = eval t (NotFrozen_Var :: env) args (pos-1) in Abs t, Lambda_Struct, p + 1
        | (u, v) :: args -> eval (ES(t, shift u v)) env args (pos-1)
        end
    | App(t, u) ->
        let t, sk, p = eval t env ((u, 0) :: args) (pos+1) in
        if p = pos + 1 then
          if sk = Struct_Frozen then let u, _, _ = eval u env [] 0 in App(t, u), Struct_Frozen, p - 1
          else App(t, u), Struct_NotFrozen, p - 1
        else t, sk, p
    | ES(t, u) ->
        let rs = ref (reduc_state_cons u) in
        let t, sk, p = eval t (Arg(rs, env) :: env) (addv args 1) pos in
        ES(t, !rs.t), sk, p

  let main t = let t, _ , _= eval t [] [] 0 in t
end

(* Here comes the abstract machine. It behaves the same as eval1_1 (environment cells + reduc_state).
  However it does not manipulate references because of a game of splitting and reconstructing
  environment right where the ref updates are normally needed (see the matchings on VAR and SUB).
  It's also possible to define this machine with references in the env for a faster (but less readable imo) algo
*)
module Eval2_0 = struct
  open Term

  type structure_kind =
    | Lambda_Struct
    | Struct_Frozen
    | Struct_NotFrozen

  type reduc_state = {t:term; sk:structure_kind; pos:int}
  let reduc_state_cons t = {t; sk=Lambda_Struct; pos=Int.max_int}

  type cell =
    | Frozen_Var | NotFrozen_Var
    | Arg of reduc_state
  and env = cell list

  type arg = term * int
  type args = arg list

  let adda args u = (u, 0) :: args
  let addv args v =
    match args with
    | [] -> []
    | (u, v') :: args -> (u, v + v') :: args

  type continuation =
    | Bind
    | Call of int * env * args
    | Struct of term * args * int
  type trace = continuation list
  
  let arg_cons u v = Arg (reduc_state_cons (shift u v))

  let rec step_down trm env trc args pos =
    let arg_cons u v = Arg (reduc_state_cons (shift u v)) in
    match trm with
    | Var k ->
        let lenv, e, renv = list_split env k in
        begin match e with
        | Frozen_Var -> step_up trm env trc args Struct_Frozen pos
        | NotFrozen_Var -> step_up trm env trc args Struct_NotFrozen pos
        | Arg rs ->
            if pos < rs.pos then step_down rs.t renv (Call(k, lenv, args) :: trc) [] pos
            else sub k rs env trc args pos
        end
    | Abs trm ->
        begin match args with
        | [] when pos = 0 -> step_down trm (Frozen_Var :: env) (Bind :: trc) [] 0
        | [] -> step_down trm (NotFrozen_Var :: env) (Bind :: trc) [] (pos-1)
        | (u, v) :: args ->
            step_down trm (arg_cons u v :: env) (Bind :: trc) (addv args (v+1)) (pos-1)
        end
    | App(trm, u) -> step_down trm env trc (adda args u) (pos+1)
    | ES (trm, u) -> step_down trm (arg_cons u 0 :: env) (Bind :: trc) (addv args 1) pos

  and step_up t env trc args sk pos =
    match env, trc, args with
    | [], [], [] when (sk = Lambda_Struct || sk = Struct_Frozen) && pos = 0 -> t
    | _, Call(k, lenv, args) :: trc, [] ->
        sub k {t; sk; pos} (lenv @ (arg_cons t 0 :: env)) trc args pos
    | _, Struct(u, args, pos) :: trc, [] ->
        step_up (App(u, t)) env trc args Struct_Frozen (pos-1)
    | Frozen_Var :: env, Bind :: trc, [] -> step_up (Abs t) env trc args Lambda_Struct 0
    | NotFrozen_Var :: env, Bind :: trc, [] -> step_up (Abs t) env trc args Lambda_Struct (pos+1)
    | _, _, (u, 0) :: args ->
        begin match sk with
        | Lambda_Struct -> assert false
        | Struct_Frozen -> step_down u env (Struct(t, args, pos) :: trc) [] 0
        | Struct_NotFrozen -> step_up (App(t, u)) env trc args Struct_NotFrozen (pos-1)
        end
    | Arg rs :: env, Bind :: trc, _ ->
        step_up (ES(t, rs.t)) env trc (addv args (-1)) sk pos
    | _ -> assert false

  and sub k rs env trc args pos =
    match rs.sk with
    | Lambda_Struct -> step_down (shift rs.t (k+1)) env trc args pos
    | _ -> step_up (Var k) env trc args rs.sk pos

  let main trm = step_down trm [] [] [] 0

end

module Eval2_1 = struct
  open Term

  type structure_kind =
    | Lambda_Struct
    | Struct_Frozen
    | Struct_NotFrozen

  type reduc_state = {t:term; sk:structure_kind; pos:int}
  let reduc_state_cons t = {t; sk=Lambda_Struct; pos=Int.max_int}

  type cell =
    | Frozen_Var | NotFrozen_Var
    | Arg of reduc_state ref
  and env = cell list

  type arg = term * int
  type args = arg list

  let adda args u = (u, 0) :: args
  let addv args v =
    match args with
    | [] -> []
    | (u, v') :: args -> (u, v + v') :: args

  type continuation =
    | Bind
    | Call of int * reduc_state ref * env * args
    | Struct of term * args * int
  type trace = continuation list
  
  let arg_cons u v = Arg (ref (reduc_state_cons (shift u v)))

  let rec step_down trm env trc args pos =
    match trm with
    | Var k ->
        begin match List.nth env k with
        | Frozen_Var -> step_up trm env trc args Struct_Frozen pos
        | NotFrozen_Var -> step_up trm env trc args Struct_NotFrozen pos
        | Arg rs ->
            let rsv = !rs in
            if pos < rsv.pos then step_down rsv.t (list_from env (k+1)) (Call(k, rs, env, args) :: trc) [] pos
            else sub k rsv env trc args pos
        end
    | Abs trm ->
        begin match args with
        | [] when pos = 0 -> step_down trm (Frozen_Var :: env) (Bind :: trc) [] 0
        | [] -> step_down trm (NotFrozen_Var :: env) (Bind :: trc) [] (pos-1)
        | (u, v) :: args ->
            step_down trm (arg_cons u v :: env) (Bind :: trc) (addv args (v+1)) (pos-1)
        end
    | App(trm, u) -> step_down trm env trc (adda args u) (pos+1)
    | ES (trm, u) -> step_down trm (arg_cons u 0 :: env) (Bind :: trc) (addv args 1) pos

  and step_up t env trc args sk pos =
    match env, trc, args with
    | [], [], [] when (sk = Lambda_Struct || sk = Struct_Frozen) && pos = 0 -> t
    | _, Call(k, rs, env, args) :: trc, [] ->
        rs := {t; sk; pos}; 
        sub k !rs env trc args pos
    | _, Struct(u, args, pos) :: trc, [] ->
        step_up (App(u, t)) env trc args Struct_Frozen (pos-1)
    | Frozen_Var :: env, Bind :: trc, [] -> step_up (Abs t) env trc args Lambda_Struct 0
    | NotFrozen_Var :: env, Bind :: trc, [] -> step_up (Abs t) env trc args Lambda_Struct (pos+1)
    | _, _, (u, 0) :: args ->
        begin match sk with
        | Lambda_Struct -> assert false
        | Struct_Frozen -> step_down u env (Struct(t, args, pos) :: trc) [] 0
        | Struct_NotFrozen -> step_up (App(t, u)) env trc args Struct_NotFrozen (pos-1)
        end
    | Arg rs :: env, Bind :: trc, _ ->
        step_up (ES(t, !rs.t)) env trc (addv args (-1)) sk pos
    | _ -> assert false

  and sub k rs env trc args pos =
    match rs.sk with
    | Lambda_Struct -> step_down (shift rs.t (k+1)) env trc args pos
    | _ -> step_up (Var k) env trc args rs.sk pos

  let main trm = step_down trm [] [] [] 0

end
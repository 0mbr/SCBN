(**
  Modules that can count/enumerate terms of various sizes with a fixed number
  of free variables.

  For clarity of algorithms, it does not comprehend any kind of memoization.
  [cardinality_partial] should be enhanced with a "memo n r" function.
  [unrank_partial] shoud be enhanced with a "constructor memoization" function.
*)

type term =
  | Var of int
  | Abs of term
  | App of term * term

(** [sum_pairs n] list all pairs of integer values that sums to [n]. 
  *)
  let sum_pairs n =
    let rec cp pairs i = match i with
    | _ when i = n -> (i, 0) :: pairs
    | _ -> cp ((i, n-i) :: pairs) (succ i)
    in
    cp [] 0

(** all integers pairs that sums to n without their symmetrical duals. *)
let sum_pairs_no_sym n =
  let rec cp pairs i =
    match i with
    | x when x > n / 2 -> pairs
    | _ -> cp ((i, n-i) :: pairs) (succ i)
  in
  cp [] 0

(** [cardinality_partial n r] computes the cardinality of the set of all PC 
    terms at range [r] and of size [n].
    
    ~ Accordingly to eois:A22094, this function is correct.
*)
let cardinality_partial n r =
  let rec cp n r =
    match n with
    | 0 -> Z.of_int r
    | _ ->
      (* cardinality of { Abs t st |t| = n-1 with one more possible free 
         variable } *)
      let abs_card = cp (pred n) (succ r) in
      (* cardinality of { t1 t2 st |t1| = i, |t2| = j } *)
      let card_of_pair i j =
        let lcard, rcard = cp i r, cp j r in
        let card = Z.mul lcard rcard in
        (* count { t1 t2 | size(t1) = j, size(t2) = i } aswell.
           mul by two is to count symnetrical duals. *)
        if i = j then card else Z.mul (Z.of_int 2) card
      in
      let app_card = List.fold_left 
                      (fun c (i, j) -> Z.add c (card_of_pair i j)) 
                      Z.zero (sum_pairs_no_sym (pred n)) 
      in
      Z.add abs_card app_card
  in
  cp n r

let msg_out_of_bound_unrank_partial_index n r i c = 
  Printf.sprintf 
    "Index %s is not suited for the set of PC terms at range %d of size %d. This \
    set's cardinality is %s."
    (Z.to_string i) r n (Z.to_string c)

(** [unrank_partial n r i] unrank the [i]th term in the set of all PC terms at
    range [r] and of size [n]. Raises Invalid_Argument in case [i] is out of
    bounds.
    
    Although the computation follows the same patterns as in 
    [cardinality_partial], the order (on tree structure) at which terms are 
    unranked is not clear.
*)
let unrank_partial n r i =
  let card = cardinality_partial n r in
  if i < Z.zero || card <= i then 
    invalid_arg (msg_out_of_bound_unrank_partial_index n r i card);
  
  let rec cp n r i =
    match n with
    | 0 -> Var (Z.to_int i)
    | _ ->
      let abs_card = cardinality_partial (pred n) (succ r) in
      if i < abs_card then Abs(cp (pred n) (succ r) i) else 
        cp_app r (Z.sub i abs_card) (sum_pairs (pred n))

  and cp_app r i pairs =
    match pairs with
    | [] -> assert false (* <=> i out of bounds, which is already dealth with. *)
    | (ls, rs) :: pairs ->
      let lcard = cardinality_partial ls r in
      let rcard = cardinality_partial rs r in
      let app_card = Z.mul lcard rcard in
      if i < app_card then
        (* let's consider c1 * c2. This can be visually represented as c2 boxes
           of size c1. Then this calculation can be seen as we take the i1-th
           index of the i2-th box. *)
        let i1 = Z.rem i lcard in
        let i2 = Z.div i lcard in
        App(cp ls r i1, cp rs r i2)
      else cp_app r (Z.sub i app_card) pairs
  in
  cp n r i
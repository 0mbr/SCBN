
type term =
  | Var of int
  | Abs of term
  | App of term * term
  | ES  of term * term

let (@<) t1 t2 = App(t1, t2)

let shift_from trm amnt from =
  if amnt = 0 then trm else
  let rec aux trm dpth =
    match trm with
    | Var k -> Var(if k >= dpth then k + amnt else k)
    | Abs trm -> Abs(aux trm (dpth + 1))
    | ES(trm, tsub) -> ES(aux trm (dpth + 1), aux tsub dpth)
    | App(trm, targ) -> App(aux trm dpth, aux targ dpth)
  in
  aux trm from

let shift trm amnt = shift_from trm amnt 0

(* Curryfied print of a term *)
let rec string_of_term t =
  Printf.(
  match t with  
  | Var k -> sprintf "%d" k
  | Abs t ->
      begin match t with
      | Abs _ -> sprintf "λ %s"  (string_of_term t)
      | Var k -> sprintf "λ. %d"  k
      | _     -> sprintf "λ. %s" (string_of_term t)
      end
  | App(tl, tr) ->
      begin match tl, tr with
      | Var k1, Var k2 -> sprintf "%d %d"    k1 k2
      | Var k , _      -> sprintf "%d (%s)"  k (string_of_term tr)
      | App _ , Var k  -> sprintf "%s %d"   (string_of_term tl) k
      | _     , Var k  -> sprintf "(%s) %d" (string_of_term tl) k
      | App _ , _ -> 
        sprintf "%s (%s)" (string_of_term tl) (string_of_term tr)
      | _ -> sprintf "(%s) (%s)" (string_of_term tl) (string_of_term tr)
      end
  | ES(t, ts) ->
      begin match t with
      | ES _ -> sprintf "%s[%s]"    (string_of_term t) (string_of_term ts)
      | Var k -> sprintf "%d[%s]"    k (string_of_term ts)
      | _     -> sprintf "(%s)[%s]" (string_of_term t) (string_of_term ts)
      end)
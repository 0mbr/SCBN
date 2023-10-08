open LambdaLib.Term
open LambdaLib.EvalSCBN

let () =

  (* let eval_1 t = Eval0.main t in *)
  let eval_2 t = Eval2_1.main t in

  let t = (Abs(Abs(Var 1 @< Var 0)) @< Abs(Abs(Var 0)))
            @< Abs(Var 0) in
  let t_result =  eval_2 t in
  Printf.printf "%s\n" (string_of_term t_result);

  let t = Abs(App(ES(App(ES(App(App(Abs(ES(Abs(Var 4), Var 3)), Var 2), Var 2), Var 1), Var 0), Var 0), Var 0)) in
  Printf.printf "%s\n" (string_of_term t);
  let t_result =  eval_2 t in
  Printf.printf "%s\n" (string_of_term t_result);

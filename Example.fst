module Example

open FStar.Tactics
open FStar.List.Tot
open JS
open JS.Ast
open JS.Translate
open JS.Ast.DSL

let rec factorial (n:nat) = 
  let open FStar.Mul in
  if n = 0 then 1 else n * (factorial (n - 1))

let rec fibonacci n =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

let main n = 
  [ ("fibonacci(" ^ string_of_int n ^ ") => " ^ string_of_int (fibonacci n))
  ; ("factorial(" ^ string_of_int n ^ ") => " ^ string_of_int (factorial n))
  ]

let _ = run_tactic (fun _ -> 
  term_to_js_files "example" (fun e -> console_log (e @@@ [EConst (CInt 5)])
                         )
                         (`main)
)


module JS.Effect
include JS.Effect.Core
module JECP = JS.Effect.Core.Primitives
include JS.Effect.TC
include JS.Effect.Utils

open JS
open JS.Ast
open JS.Ast.DSL
open FStar.Tactics

let computation_to_js_files (basename: string) (term: unit -> Js unit): Tac unit =
  term_to_js_files' (primitives @ JECP.primitives) basename
    (fun e -> SExpr (e @@@ []))
    (quote term)

open JS.Effect.TC
let f (): Js unit
  = let _ = globalThis.["console"].["log"].(
    list_to_array [!1;!2;!3;!4;!5]
  ) in
    ()

let _ = run_tactic (fun _ -> 
    computation_to_js_files "test-new" f
  )


module JS

open FStar.Tactics
open FStar.Reflection
open FStar.List.Tot

open JS.Ast
open JS.Ast.Utils
open JS.Ast.Print
open JS.Ast.DSL
open JS.Translate

let writeToFile file content
   = let _ = launch_process "sh" ["-c"; "cat - > " ^ file] content in ()

let blacklist = map explode_qn [`%int]

let (!) = JSId None
let (!!) n = EVar (JSId None n)

let console_log (v: js_expr)
  : js_stmt
  = let console = !!"console" in
    let console_log = console.(str "log") in
    SExpr (console_log @@@ [v])
    
let primitives: list (name * js_stmt)
  = let h (name: string) (args: list js_id) (body: js_expr) =
        let name = explode_qn name in
        let jid = fv_to_js_id (pack_fv name) None in
        let mk_e body arg = eFunction None [arg] (SReturn body) in
        let mk_curried args body = fold_left mk_e body (rev args) in
        name, SLet jid (mk_curried args body)
    in
    [ h (`%int) [] (str "Type:INT")
    ; h (`%nat) [] (str "Type:NAT")
    ; h (`%string) [] (str "Type:STRING")
    ; h (`%(+)) [!"x";!"y"] (EBinaryOp JsBin_Plus (!!"x") (!!"y"))
    ; h (`%(op_Multiply)) [!"x";!"y"] (EBinaryOp JsBin_Mul (!!"x") (!!"y"))
    ; h (`%(FStar.Mul.op_Star)) [!"x";!"y"] (EBinaryOp JsBin_Mul (!!"x") (!!"y"))
    ; h (`%op_Subtraction) [!"x";!"y"] (EBinaryOp JsBin_Minus (!!"x") (!!"y"))
    ; h (`%op_Equality) [!"tvar";!"x";!"y"] (EBinaryOp JsBin_Eq (!!"x") (!!"y"))
    ; h (`%op_LessThanOrEqual) [!"x";!"y"] (EBinaryOp JsBin_Le (!!"x") (!!"y"))
    ; h (`%string_of_int) [!"s"] (EBinaryOp JsBin_Plus (EConst (CString "")) (!!"s"))
    ; h (`%op_Hat) [!"x";!"y"] (EBinaryOp JsBin_Plus (!!"x") (!!"y"))
    ]

let term_to_js_stmt (wrapper: js_expr -> js_stmt) (term: term): Tac js_stmt = 
  let blacklist = map fst primitives @ blacklist in
  let js_body = term_to_js_with_dep term wrapper blacklist in
  let js_primitive = sseq (map snd primitives) in
  let js_code = js_primitive `SSeq` js_body in
  js_code

let term_to_js wrapper (term: term): Tac string =
  string_of_jsstmt (term_to_js_stmt wrapper term)

let term_to_js_files (basename: string) wrapper (term: term): Tac unit =
  let stmt = term_to_js_stmt wrapper term in
  writeToFile (basename ^ ".js") (string_of_jsstmt stmt);
  let sm = sourcemap_of_jsstmt stmt in
  let l = map (fun (s, e, r) -> "[" ^ Doc.string_of_position s ^ " .. " ^ Doc.string_of_position e ^ "] => " ^ Doc.string_of_range_info r ) sm in
  writeToFile (basename ^ ".sourcemap") (String.concat "\n" l ^ "\n\n\n\n\n")



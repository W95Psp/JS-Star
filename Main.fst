module Main

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
    ; h (`%(+)) [!"x";!"y"] (EBinaryOp JsBin_Plus (!!"x") (!!"y"))
    ; h (`%op_Subtraction) [!"x";!"y"] (EBinaryOp JsBin_Minus (!!"x") (!!"y"))
    ; h (`%op_Equality) [!"tvar";!"x";!"y"] (EBinaryOp JsBin_Eq (!!"x") (!!"y"))
    ; h (`%op_LessThanOrEqual) [!"x";!"y"] (EBinaryOp JsBin_Le (!!"x") (!!"y"))
    ]


let rec f (x: int): int = 
  if x <= 0 then 0
           else x + f (x - 1)
           
let rec test (n: int): list int = 
  let t = f n in
  if n <= 0
  then [t]
  else t::test (n-1)

let rec sum (l: list int): int
  = match l with
  | [] -> 0
  | hd::tl -> hd + sum tl

let hey (n: int): int
  = sum (test 4) + fold_left (fun y x -> y + x) 0 (test 4)

let tup2_to_string (x, y) = "(" ^ string_of_int x ^ ", " ^ string_of_int y ^ ")"

let range_to_string (r: range) = 
    let r = inspect_range r in
    "{" ^ r.file_name ^ " : " ^ tup2_to_string r.start_pos ^ "-> " ^ tup2_to_string r.end_pos ^ "}"

let _ = run_tactic (fun _ ->
  let blacklist = map fst primitives @ blacklist in
  let x = term_to_js_with_dep (`(
    hey
  )) (fun e -> console_log (e @@@ [EConst (CInt 5)]) ) blacklist in
  let x = sseq (map snd primitives) `SSeq` (x) in
  writeToFile "out.js" (string_of_jsstmt x);
  let sm = sourcemap_of_jsstmt x in
  let l = map (fun (s, e, r) -> "[" ^ Doc.string_of_position s ^ " .. " ^ Doc.string_of_position e ^ "] => " ^ Doc.string_of_range_info r ) sm in
  writeToFile "out.sourcemap" (String.concat "\n" l ^ "\n\n\n\n\n")
)


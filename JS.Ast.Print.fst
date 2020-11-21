module JS.Ast.Print

open FStar.String
open FStar.List.Tot
open JS.Ast
open JS.Ast.Utils

open Output
let output_of_js_unary_op = function
  | JsUnary_Minus -> [OKeyword true "+"] 
  | JsUnary_Plus  -> [OKeyword true "-"] 
  | JsUnary_Not   -> [OKeyword true "!"] 
  | JsUnary_TypeOf-> [OKeyword true "typeof"]

let output_of_js_binary_op = function
  | JsBin_Minus      -> [OKeyword true "-"]
  | JsBin_Plus       -> [OKeyword true "+"]
  | JsBin_Mul        -> [OKeyword true "*"]
  | JsBin_Div        -> [OKeyword true "/"] 
  | JsBin_InstanceOf -> [OKeyword true "instanceof"]
  | JsBin_Eq         -> [OKeyword true "==="]
  | JsBin_Lt         -> [OKeyword true "<"]
  | JsBin_Le         -> [OKeyword true "<="]
  | JsBin_Gt         -> [OKeyword true ">"] 
  | JsBin_Ge         -> [OKeyword true ">="]
  | JsBin_And        -> [OKeyword true "&&"]
  | JsBin_Or         -> [OKeyword true "||"]

let print_js_const (c: js_const)
  : list output
  = match c with
  | CNull -> [OKeyword true "null"]
  | CThis -> [OKeyword true "this"]
  | CUndefined -> [OKeyword true "undefined"]
  | CSymbol -> [OKeyword true "Symbol()"]
  | CString str -> [OQuote str] // Todo escape
  | CInt n -> [OKeyword true (string_of_int n)]
  | CBool b -> [OKeyword true (if b then "true" else "false")]

let curly = OPair true "{" "}"
let sq = OPair false "[" "]"
let par = OPair false "(" ")"
let semicolon = OKeyword false ";"
let klet      = OKeyword true "let"
let kequal    = OKeyword true "="
let comma     = OKeyword true ","
let dot       = OKeyword false "."

let print_js_ident i: list output = [OIdentitier (range_of_jsid i) (name_of_jsid i)]

let rec print_js_stmt (s: js_stmt)
  = match s with
  | SFunction fn -> print_js_function fn
  | SBlock body -> [curly (print_js_stmt body)]
  | SExpr expr -> print_js_expr expr @ [semicolon]
  | SLet name body -> [klet] @ print_js_ident name @ [kequal] @ print_js_expr body @ [semicolon]
  | SAssign lhs nvalue -> print_js_expr lhs @ [kequal] @ print_js_expr nvalue @ [semicolon]
  | SIf cond b_then b_else -> [OKeyword true "if"; par (print_js_expr cond); curly (print_js_stmt b_then); 
                              match b_else with
                             | Some br -> ONest [OKeyword true "else"; curly (print_js_stmt br)]
                             | _ -> OEmpty
                             ]
  | SWhile cond body -> [OKeyword true "while"; par (print_js_expr cond); curly (print_js_stmt body)]
  | SSeq a b -> print_js_stmt a @ print_js_stmt b
  | SReturn v -> [OKeyword true "return" ] @ print_js_expr v @ [semicolon]
  | SThrow ex -> [OKeyword true "throw" ] @ print_js_expr ex @ [semicolon]
  | SNoOp -> []
and print_js_expr (e: js_expr)
  = match e with
  | EAbs args body -> [par ([par [OSeparatedList comma (map (fun a -> ONest (print_js_ident a)) args)]; OKeyword true "=>"] @ print_js_expr body)]
  | EFunction fn -> [par (print_js_function fn)]
  | EVar name -> print_js_ident name
  | EApp f this args ->  let all = let args' = map (fun a -> ONest (print_js_expr a)) (smaller e args) in
                        if this=EConst CNull || this=EConst CUndefined
                        then print_js_expr f @ [par [OSeparatedList comma args']]
                        else print_js_expr f @ [dot;OIdentitier None "apply"] @ [par (print_js_expr this @ [comma; sq [OSeparatedList comma args']])]
                        in [par all]
  | ENew cons args ->  let args' = map (fun a -> ONest (print_js_expr a)) (smaller e args) in
                      [par ([OKeyword true "new"] @ print_js_expr cons @ [par [OSeparatedList comma args']])]
  | EGet o key ->  print_js_expr o @ [sq (print_js_expr key)]
  | EAssign o v -> [par (print_js_expr o @ [kequal] @ print_js_expr v) ]
  | ESeq a b -> [par (print_js_expr a @ [comma] @ print_js_expr b)]
  | EBinaryOp o l r -> [par (print_js_expr l @ output_of_js_binary_op o @ print_js_expr r)]
  | EUnaryOp o v -> [par (output_of_js_unary_op o @ print_js_expr v)]
  | EConst c -> print_js_const c
and print_js_function (JSFunction id args body)
  = [ OKeyword true "function"
    ; (match id with | None -> OEmpty
                    | Some id -> ONest (print_js_ident id))
    ; par [OSeparatedList comma (map (fun a -> ONest (print_js_ident a)) args)]
    ; curly (print_js_stmt body)
    ]


let string_of_js_expr (e: js_expr) = string_of_output (ONest (print_js_expr e))
let string_of_js_stmt (e: js_stmt) = string_of_output (ONest (print_js_stmt e))



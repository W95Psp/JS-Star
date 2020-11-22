module JS.Ast.Print

open FStar.String
open FStar.List.Tot
open JS.Ast
open JS.Ast.Utils

open Output

let output_of_js_unary_op = function
  | JsUnary_Not    -> str "!"
  | JsUnary_Plus   -> str "+"
  | JsUnary_Minus  -> str "-"
  | JsUnary_TypeOf -> str "typeof" <+> s
  | JsUnary_New    -> str "new" <+> s

let output_of_js_binary_op = function
  | JsBin_Sequence             -> (fun x y -> x <+> str ";" <+> y)
  | JsBin_Assign               -> (fun x y -> x <+> str "=" <+> y)
  | JsBin_And                  -> (fun x y -> x <+> str "&&" <+> y)
  | JsBin_Or                   -> (fun x y -> x <+> str "||" <+> y)
  | JsBin_LooseEq              -> (fun x y -> x <+> str "==" <+> y)
  | JsBin_Eq                   -> (fun x y -> x <+> str "===" <+> y)
  | JsBin_Lt                   -> (fun x y -> x <+> str "<" <+> y)
  | JsBin_Le                   -> (fun x y -> x <+> str "<=" <+> y)
  | JsBin_Gt                   -> (fun x y -> x <+> str ">" <+> y)
  | JsBin_Ge                   -> (fun x y -> x <+> str ">=" <+> y)
  | JsBin_InstanceOf           -> (fun x y -> x <+> s <+> str "instanceof" <+> s <+> y)
  | JsBin_Minus                -> (fun x y -> x <+> str "-" <+> y)
  | JsBin_Plus                 -> (fun x y -> x <+> str "+" <+> y)
  | JsBin_Mul                  -> (fun x y -> x <+> str "*" <+> y)
  | JsBin_Exp                  -> (fun x y -> x <+> str "**" <+> y)
  | JsBin_Div                  -> (fun x y -> x <+> str "/" <+> y)
  | JsBin_Rem                  -> (fun x y -> x <+> str "%" <+> y)
  | JsBin_MemberAccess         -> (fun x y -> x <+> str "[" <+> y <+> str "]")
  | JsBin_ComputedMemberAccess -> (fun x y -> x <+> str "[" <+> y <+> str "]")

let escape_string_simple_quote (s: string): string
  = replace_char_str "'" "\\'" (replace_char_str "\\" "\\\\" s)

let print_js_const #a (c: js_const): doc a
  = match c with
  | CNull      -> str "null"
  | CThis      -> str "this"
  | CUndefined -> str "undefined"
  | CSymbol    -> str "Symbol()"
  | CString  s -> str "'" <+> str (escape_string_simple_quote s) <+> str "'"
  | CInt     n -> str (string_of_int n)
  | CBool    b -> str (if b then "true" else "false")

let opt (f: 'b -> doc 'a) = function | Some x -> f x | None -> empty

type doc = doc (option range_info)

let print_js_ident i: doc
  = annote (str (name_of_jsid i)) (range_of_jsid i)

let indented_brace_block body = lbrace <+> indent (nl <+>  body) <+> nl <+> rbrace

let space = s

let rec print_js_stmt (s: js_stmt)
  = match s with
  | SFunction fn -> print_js_function fn
  | SBlock body -> indented_brace_block (print_js_stmt body)
  | SExpr expr -> print_js_expr expr <+> semicolon <+> nl
  | SLet name body -> klet <+> space <+> print_js_ident name <+> kequal <+> print_js_expr body <+> semicolon <+> nl
  | SAssign lhs nvalue -> print_js_expr lhs <+> kequal <+> print_js_expr nvalue <+> semicolon <+> nl
  | SIf cond b_then b_else ->   str "if" <+> space <+> lparen <+> print_js_expr cond <+> rparen
                           <+> indented_brace_block (print_js_stmt b_then)
                           <+> ( match b_else with
                               | Some b_else -> str "else" <+> indented_brace_block (print_js_stmt b_else)
                               | _           -> empty
                               )
  | SWhile cond body -> str "while" <+> lparen <+> print_js_expr cond <+> rparen <+> indented_brace_block (print_js_stmt body)
  | SSeq a b -> print_js_stmt a <+> print_js_stmt b
  | SReturn v -> str "return" <+> space <+> print_js_expr v <+> semicolon <+> nl
  | SThrow ex -> str "throw" <+> space <+> print_js_expr ex <+> semicolon <+> nl
  | SNoOp -> empty
and print_js_expr (e: js_expr)
  = match e with
  | EArrowFun args body -> lparen <+> lparen <+> concatSep comma (map (fun a -> print_js_ident a) args) <+> rparen <+> space <+> str "=>" <+> space <+> print_js_expr body
                      <+> rparen
  | EFunction fn -> lparen <+> print_js_function fn <+> rparen
  | EVar name -> print_js_ident name
  | EApp f args -> let args' = map (fun a -> print_js_expr a) (smaller e args) in
                  lparen <+> print_js_expr f <+> lparen <+> concatSep comma args' <+> rparen <+> rparen
  | ENew f args -> let args' = map (fun a -> print_js_expr a) (smaller e args) in
                  lparen <+> str "new" <+> space <+> print_js_expr f <+> lparen <+> concatSep comma args' <+> rparen <+> rparen
  | EBinaryOp o l r -> lparen <+> output_of_js_binary_op o (print_js_expr l) (print_js_expr r) <+> rparen
  | EUnaryOp o v -> lparen <+> output_of_js_unary_op o <+> print_js_expr v <+> rparen
  | EConst c -> print_js_const c
// and print
and print_js_function (JSFunction id args body)
  =   str "function" <+> space <+> opt print_js_ident id
  <+> lparen <+> concatSep comma (map (fun a -> print_js_ident a) args) <+> rparen
  <+> indented_brace_block (print_js_stmt body)

let string_of_js_expr (e: js_expr) = doc_to_string (print_js_expr e)
let string_of_js_stmt (e: js_stmt) = doc_to_string (print_js_stmt e)




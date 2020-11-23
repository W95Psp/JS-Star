module JS.Ast.Print

open FStar.String
open FStar.List.Tot
open JS.Ast
open JS.Ast.Utils

open Doc


/// Mapping from unary operators to `doc _`
let output_of_js_unary_op = function
  | JsUnary_Not    -> str "!"
  | JsUnary_Plus   -> str "+"
  | JsUnary_Minus  -> str "-"
  | JsUnary_TypeOf -> str "typeof" <+> space
  | JsUnary_New    -> str "new" <+> space

/// Mapping from binary operators to `doc _`
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
  | JsBin_InstanceOf           -> (fun x y -> x <+> space <+> str "instanceof" <+> space <+> y)
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

let doc_of_jsconst #a (c: js_const): doc a
  = match c with
  | CNull      -> str "null"
  | CThis      -> str "this"
  | CUndefined -> str "undefined"
  | CSymbol    -> str "Symbol()"
  | CString  s -> str "'" <+> str (escape_string_simple_quote s) <+> str "'"
  | CInt     n -> str (string_of_int n)
  | CBool    b -> str (if b then "true" else "false")

let opt (f: 'b -> doc 'a) = function | Some x -> f x | None -> empty

let doc_of_jsid i
  = let body = str (name_of_jsid i) in
    match range_of_jsid i with
  | Some a -> annote body a
  | _ -> body

let indented_brace_block body = lbrace <+> indent (nl <+>  body) <+> nl <+> rbrace

let rec smaller' #t p ref (l: list t {l << ref /\ for_all p l})
  : (r: list (x: t {x << ref /\ p x}) { length l == length r })
  = match l with
  | [] -> []
  | hd::tl -> hd::smaller' #t p ref tl

let rec smaller #t ref (l: list t {l << ref})
  : (r: list (x: t {x << ref}) { length l == length r })
  = match l with
  | [] -> []
  | hd::tl -> hd::smaller #t ref tl

let rec doc_of_jsstmt (s: js_stmt)
  = match s with
  | SFunction fn -> doc_of_jsfunction fn
  | SBlock body -> indented_brace_block (doc_of_jsstmt body)
  | SExpr expr -> doc_of_jsexpr expr <+> semicolon <+> nl
  | SLet name body -> klet <+> space <+> doc_of_jsid name <+> kequal <+> doc_of_jsexpr body <+> semicolon <+> nl
  | SAssign lhs nvalue -> doc_of_jsexpr lhs <+> kequal <+> doc_of_jsexpr nvalue <+> semicolon <+> nl
  | SIf cond b_then b_else ->   str "if" <+> space <+> lparen <+> doc_of_jsexpr cond <+> rparen
                           <+> indented_brace_block (doc_of_jsstmt b_then)
                           <+> ( match b_else with
                               | Some b_else -> str "else" <+> indented_brace_block (doc_of_jsstmt b_else)
                               | _           -> empty
                               )
  | SWhile cond body -> str "while" <+> lparen <+> doc_of_jsexpr cond <+> rparen <+> indented_brace_block (doc_of_jsstmt body)
  | SSeq a b -> doc_of_jsstmt a <+> doc_of_jsstmt b
  | SReturn v -> str "return" <+> space <+> doc_of_jsexpr v <+> semicolon <+> nl
  | SThrow ex -> str "throw" <+> space <+> doc_of_jsexpr ex <+> semicolon <+> nl
  | SNoOp -> empty
and doc_of_jsexpr (e: js_expr)
  = match e with
  | EArrowFun args body -> lparen <+> lparen <+> concatSep comma (map (fun a -> doc_of_jsid a) args) <+> rparen <+> space <+> str "=>" <+> space <+> doc_of_jsexpr body
                      <+> rparen
  | EFunction fn -> lparen <+> doc_of_jsfunction fn <+> rparen
  | EVar name -> doc_of_jsid name
  | EApp f args -> let args' = map (fun a -> doc_of_jsexpr a) (smaller e args) in
                  lparen <+> doc_of_jsexpr f <+> lparen <+> concatSep comma args' <+> rparen <+> rparen
  | ENew f args -> let args' = map (fun a -> doc_of_jsexpr a) (smaller e args) in
                  lparen <+> str "new" <+> space <+> doc_of_jsexpr f <+> lparen <+> concatSep comma args' <+> rparen <+> rparen
  | EBinaryOp o l r -> lparen <+> output_of_js_binary_op o (doc_of_jsexpr l) (doc_of_jsexpr r) <+> rparen
  | EUnaryOp o v -> lparen <+> output_of_js_unary_op o <+> doc_of_jsexpr v <+> rparen
  | EConst c -> doc_of_jsconst c
and doc_of_jsfunction (JSFunction id args body)
  =   str "function" <+> space <+> opt doc_of_jsid id
  <+> lparen <+> concatSep comma (map (fun a -> doc_of_jsid a) args) <+> rparen
  <+> indented_brace_block (doc_of_jsstmt body)

let string_of_jsexpr (e: js_expr) = doc_to_string (doc_of_jsexpr e)
let string_of_jsstmt (e: js_stmt) = doc_to_string (doc_of_jsstmt e)
let sourcemap_of_jsstmt (e: js_stmt): list (position & position & range_info)
  = doc_to_annotations (doc_of_jsstmt e)


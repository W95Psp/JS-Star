module JS.Ast

open FStar.String
open FStar.List.Tot
module R = FStar.Reflection
open Output

type js_unary_op = 
  | JsUnary_Minus | JsUnary_Plus | JsUnary_Not | JsUnary_TypeOf
  | JsUnary_New
type js_binary_op =
  | JsBin_LooseEq | JsBin_Eq
  | JsBin_Lt | JsBin_Le | JsBin_Gt | JsBin_Ge | JsBin_And | JsBin_Or
  | JsBin_Minus | JsBin_Plus | JsBin_Mul | JsBin_Div
  | JsBin_Rem | JsBin_Exp
  | JsBin_InstanceOf
  | JsBin_FunctionCall
  | JsBin_MemberAccess
  | JsBin_ComputedMemberAccess
  | JsBin_Assign
  | JsBin_Sequence

type associatvity = | LeftToRight | RightToLeft

let precedence_of_unary_op = function
  | JsUnary_Not    -> 17, Some RightToLeft
  | JsUnary_Plus   -> 17, Some RightToLeft
  | JsUnary_Minus  -> 17, Some RightToLeft
  | JsUnary_TypeOf -> 17, Some RightToLeft
  | JsUnary_New    -> 19, Some RightToLeft

let precedence_of_binary_op = function
  | JsBin_Sequence             -> 1, Some LeftToRight
  | JsBin_Assign               -> 3, Some RightToLeft
  | JsBin_And                  -> 7, Some LeftToRight
  | JsBin_Or                   -> 8, Some LeftToRight
  | JsBin_LooseEq              -> 11, Some LeftToRight
  | JsBin_Eq                   -> 11, Some LeftToRight
  | JsBin_Lt                   -> 12, Some LeftToRight
  | JsBin_Le                   -> 12, Some LeftToRight
  | JsBin_Gt                   -> 12, Some LeftToRight
  | JsBin_Ge                   -> 12, Some LeftToRight
  | JsBin_InstanceOf           -> 12, Some LeftToRight
  | JsBin_Minus                -> 14, Some LeftToRight
  | JsBin_Plus                 -> 14, Some LeftToRight
  | JsBin_Mul                  -> 15, Some LeftToRight
  | JsBin_Exp                  -> 15, Some RightToLeft
  | JsBin_Div                  -> 15, Some LeftToRight
  | JsBin_Rem                  -> 15, Some LeftToRight
  | JsBin_FunctionCall         -> 20, Some LeftToRight
  | JsBin_MemberAccess         -> 20, Some LeftToRight
  | JsBin_ComputedMemberAccess -> 20, Some LeftToRight

type js_id = | JSId : range:option range_info -> s:string -> js_id
             | ReservedId : nat -> js_id

let js_id_eq (i j: js_id)
  = match i, j with
  | JSId ir is, JSId jr js -> is = js
  | ReservedId i, ReservedId j -> i = j
  | _ -> false

type js_expr
  = | EArrowFun: args: list js_id -> body: js_expr -> js_expr
    | EFunction: fn:js_function -> js_expr
    | EVar: name: js_id -> js_expr
    | EApp: fn: js_expr -> args: list js_expr -> js_expr
    | EUnaryOp: op:js_unary_op -> v:js_expr -> js_expr
    | EBinaryOp: op:js_binary_op -> v:js_expr -> w:js_expr -> js_expr
    | EConst: c: js_const -> js_expr
and js_stmt =
    | SFunction: fn:js_function -> js_stmt
    | SBlock: body:js_stmt -> js_stmt
    | SExpr: expr:js_expr -> js_stmt
    | SLet: name:js_id -> body:js_expr -> js_stmt
    | SAssign: name:js_expr -> body:js_expr -> js_stmt
    | SSeq: a:js_stmt -> b:js_stmt -> js_stmt
    | SIf: cond:js_expr -> b_then:js_stmt -> b_else:option js_stmt -> js_stmt
    | SWhile: cond:js_expr -> b_then:js_stmt -> js_stmt
    | SReturn: e: js_expr -> js_stmt
    | SThrow: e: js_expr -> js_stmt
    | SNoOp
and js_function = | JSFunction: name:option js_id -> args:list js_id -> body: js_stmt -> js_function
and js_const =
    | CNull | CThis | CUndefined | CSymbol
    | CString: string -> js_const
    | CInt: int -> js_const
    | CBool: bool -> js_const


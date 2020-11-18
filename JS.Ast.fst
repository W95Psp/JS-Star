module JS.Ast

open FStar.String
open FStar.List.Tot

type mrange = int * int * int

type js_unary_op = | JsUnary_Minus | JsUnary_Plus | JsUnary_Not | JsUnary_TypeOf
type js_binary_op =
  | JsBin_Eq | JsBin_Lt | JsBin_Le | JsBin_Gt | JsBin_Ge | JsBin_And | JsBin_Or
  | JsBin_Minus | JsBin_Plus | JsBin_Mul | JsBin_Div | JsBin_InstanceOf

type js_id = | JSId : range:option mrange -> s:string -> js_id
             | ReservedId : nat -> js_id

type js_expr
  = | EAbs: args: list js_id -> body: js_expr -> js_expr
    | EFunction: fn:js_function -> js_expr
    | EVar: name: js_id -> js_expr
    | EApp: f:js_expr -> this:js_expr -> args:list js_expr -> js_expr
    | ENew: cons:js_expr -> args:list js_expr -> js_expr
    | EGet: o:js_expr -> key:js_expr -> js_expr
    | EAssign: o:js_expr -> v:js_expr -> js_expr
    | ESeq: a:js_expr -> b:js_expr -> js_expr
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



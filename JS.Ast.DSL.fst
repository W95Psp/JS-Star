module JS.Ast.DSL

open JS.Ast
open LowStar.BufferOps

let (!.)   = EUnaryOp JsUnary_Not
let uplus   = EUnaryOp JsUnary_Plus
let typeof = EUnaryOp JsUnary_TypeOf
let new_   = ENew

let id x = EVar (JSId None x)

let _ = !. (id "x")

let ( >| ) = EBinaryOp JsBin_Sequence
let ( :=  ) = EBinaryOp JsBin_Assign
let ( &&. ) = EBinaryOp JsBin_And
let ( ||.  ) = EBinaryOp JsBin_Or
let ( ==. ) = EBinaryOp JsBin_LooseEq
let ( ===. ) = EBinaryOp JsBin_Eq
let ( <. ) = EBinaryOp JsBin_Lt
let ( <=. ) = EBinaryOp JsBin_Le
let ( >. ) = EBinaryOp JsBin_Gt
let ( >=. ) = EBinaryOp JsBin_Ge
let instanceof = EBinaryOp JsBin_InstanceOf
let ( -. ) = EBinaryOp JsBin_Minus
let ( +.  ) = EBinaryOp JsBin_Plus
let ( *.  ) = EBinaryOp JsBin_Mul
let ( **. ) = EBinaryOp JsBin_Exp
let ( /.  ) = EBinaryOp JsBin_Div
let ( %.  ) = EBinaryOp JsBin_Rem
let op_ = EBinaryOp JsBin_MemberAccess
let op_Array_Access = EBinaryOp JsBin_ComputedMemberAccess
let (<-.) = SAssign 

let ( @@@ ) = EApp
let this = EConst CThis
let null = EConst CNull
let undefined = EConst CUndefined



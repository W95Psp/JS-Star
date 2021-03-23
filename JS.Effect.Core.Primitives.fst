module JS.Effect.Core.Primitives

open FStar.Tactics
open FStar.Reflection
open FStar.List.Tot

open JS.Ast
open JS.Ast.Utils
open JS.Ast.Print
open JS.Ast.DSL
open JS.Translate
module C = JS.Effect.Core

let (!) = JSId None
let (!!) n = EVar (JSId None n)

let primitives: list (name * js_stmt)
  = let h (name: string) (args: list js_id) (body: js_expr) =
        let name = explode_qn name in
        let jid = fv_to_js_id (pack_fv name) None in
        let mk_e body arg = eFunction None [arg] (SReturn body) in
        let mk_curried args body = fold_left mk_e body (rev args) in
        name, SLet jid (mk_curried args body)
    in
    [ h (`%C.js_get_property) [!"o";!"k"] (EBinaryOp JsBin_ComputedMemberAccess (!!"o") (!!"k"))
    ; h (`%C.js_set_property) [!"o";!"k";!"v"] (EBinaryOp JsBin_Assign (EBinaryOp JsBin_ComputedMemberAccess (!!"o") (!!"k")) (!!"v"))
    ; h (`%C.js_remove) [!"o";!"k"] (EConst (CString "TODO")) // : fn:jsval -> key:jsval -> Js jsval
    ; h (`%C.null) [] (EConst CNull) // : jsval
    ; h (`%C.globalThis) [] (EVar !"globalThis") // : jsval
    ; h (`%C.to_jsval) [!"typ";!"x"] (EVar !"x") // : 'a -> Js jsval
    ; h (`%C.unsafe_coerce_jsval) [!"typ";!"x"] (!!"x") // : #a:Type -> jsval -> Js a
    ; h (`%C.js_call) [!"fn"] (EApp (!!"fn") []) // : fn:jsval -> Js jsval
    ; h (`%C.js_new) [!"fn"] (ENew (!!"fn") []) // : fn:jsval -> Js jsval
    ; h (`%C.js_bind_this) [!"fn";!"t"] ( (!!"fn").(EConst (CString "bind")) @@@ [!!"t"] ) // : fn:jsval -> this:jsval -> Js jsval
    ; h (`%C.js_bind_arg) [!"fn";!"a"] ( (!!"fn").(EConst (CString "bind")) @@@ [EConst CUndefined; !!"a"] ) // : fn:jsval -> this:jsval -> Js jsval
    
    ; h (`%C.jsval) [] (EConst (CString "Type:jsval")) // : fn:jsval -> Js jsval
    ]



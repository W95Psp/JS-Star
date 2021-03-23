module JS.Effect.Core

val jsval: eqtype

new_effect JS = DIV
unfold
let pure_null_wp (a: Type) (p: pure_post a) = forall (any_result: a). p any_result
sub_effect DIV ~> JS { lift_wp = purewp_id }
effect Js (a: Type) = JS a (pure_null_wp a)

// keys `k` are `jsval` since `k` can be either string or symbols
val js_get_property: o:jsval -> k: jsval -> Js jsval
val js_set_property: o:jsval -> k: jsval -> v: jsval -> Js jsval
val js_remove: fn:jsval -> key:jsval -> Js jsval

val null: jsval
val globalThis: jsval

val to_jsval: 'a -> Js jsval
val unsafe_coerce_jsval: #a:Type -> jsval -> Js a

val js_call: fn:jsval -> Js jsval
val js_new: fn:jsval -> Js jsval

val js_bind_this: fn:jsval -> this:jsval -> Js jsval
val js_bind_arg: fn:jsval -> arg:jsval -> Js jsval


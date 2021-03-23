module JS.Effect.TC

open JS.Effect.Core
open FStar.Tactics.Typeclasses

class castableToProperty a = {
  cast_to_property: a -> Js jsval;
}

#push-options "--print_implicits"

let _ = MkcastableToProperty

let _: castableToProperty int -> int -> Js _ = __proj__MkcastableToProperty__item__cast_to_property


instance jsvalKey: castableToProperty jsval
  = { cast_to_property = id }
instance stringKey: castableToProperty string
  = { cast_to_property = to_jsval }
instance intKey: castableToProperty int
  = { cast_to_property = to_jsval }

class accessPropertySyntax a 
  = { access: jsval -> a -> Js jsval }

class setPropertySyntax a b =
  { set: jsval -> a -> b -> Js jsval }

instance castableToProperty_accessPropertySyntax
  a {| castableToProperty a |}: accessPropertySyntax a
  = { access = (fun o k -> js_get_property o (cast_to_property k)) }

instance castableToProperty_setPropertySyntax
  a {| castableToProperty a |}: setPropertySyntax a jsval
  = { set = (fun o k v -> js_set_property o (cast_to_property k) v) }

instance castableToProperty_setPropertySyntax'
  a b {| castableToProperty a |}: setPropertySyntax a b
  = { set = (fun o k v -> js_set_property o (cast_to_property k) (to_jsval v)) }

let op_String_Access {| accessPropertySyntax 'a |}: jsval -> 'a -> Js jsval = access
let op_String_Assignement {| setPropertySyntax 'a 'b |}: jsval -> 'a -> 'b -> Js jsval = set


class callableSyntax fn args =
  { call: fn -> args -> Js jsval }

let op_Array_Access {| callableSyntax 'f 'a |}: 'f -> 'a -> Js jsval = call

instance call0: callableSyntax jsval unit = { call = (fun fn _ -> js_call fn) }
instance call1: callableSyntax jsval jsval = { call = (fun fn arg -> js_call (js_bind_arg fn arg)) }
instance call2: callableSyntax jsval (jsval*jsval) = { call = (fun fn (arg0,arg1) -> fn.(arg0).(arg1) ) }
instance call3: callableSyntax jsval (jsval*jsval*jsval) = { call = (fun fn (arg0,arg1,arg2) -> fn.(arg0,arg1).(arg2) ) }
instance call4: callableSyntax jsval (jsval*jsval*jsval*jsval) = { call = (fun fn (arg0,arg1,arg2,arg3) -> fn.(arg0,arg1,arg2).(arg3) ) }
instance call5: callableSyntax jsval (jsval*jsval*jsval*jsval*jsval) = { call = (fun fn (arg0,arg1,arg2,arg3,arg4) -> fn.(arg0,arg1,arg2,arg3).(arg4) ) }

instance call' #t {| callableSyntax jsval t |}: callableSyntax (unit -> Js jsval) t
  = { call = (fun (f: unit -> Js jsval) (v: t) -> (f ()).(v) ) }

type mk_new a = | New: v:a -> mk_new a

instance call'' #t {| callableSyntax 'a t |}: callableSyntax (mk_new 'a) t
  = { call = (fun (f: mk_new 'a) (v: t) -> (New?.v f).(v) ) }

let (!) (v:'a) = to_jsval v


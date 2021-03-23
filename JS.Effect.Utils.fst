module JS.Effect.Utils

open JS.Effect.Core
open JS.Effect.TC

let rec fold_left (f: 'a -> 'b -> Js 'a) (x: 'a) (l: list 'b): Js 'a = match l with
  | [] -> x
  | hd::tl -> fold_left f (f x hd) tl

let rec map (f: 'a -> Js 'b) (l: list 'a): Js (list 'b) 
  = match l with
  | [] -> []
  | hd::tl -> f hd::map f tl

let js_bind_n: (fn:jsval) -> (args:list jsval) -> Js jsval
  = fold_left js_bind_arg

let js_call_n (fn:jsval) (args:list jsval): Js jsval
  = js_call (js_bind_n fn args)

let js_call_n' (fn:jsval) (this: jsval) (args:list jsval): Js jsval
  = js_call ((js_bind_n (js_bind_this fn this) args))

let js_new_n (fn:jsval) (args:list jsval): Js jsval
  = js_new (js_bind_n fn args)

let object (): Js jsval
  = globalThis.["Object"]
  
let array (): Js jsval
  = globalThis.["Array"]

let list_to_array (l: list jsval): Js jsval
  = let arr = (New array).( () ) in
    fold_left (fun _ v -> 
      let _ = (js_bind_this arr.["push"] arr).(v) in
      ()
    ) () l;
    arr

let parseInt (o: jsval): Js int
  = unsafe_coerce_jsval (globalThis.["parseInt"].(o))

let rec array_from_list (arr: jsval) (n: nat): Js (list jsval)
  = if parseInt arr.["length"] >= n
    then []
    else arr.[!n] :: array_from_list arr (n+1)



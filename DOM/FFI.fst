module FFI

type js_ref = | JsRef: n:nat -> js_ref 

open FStar.FunctionalExtensionality

noeq
type js_type_description: Type0
  = | JSBool | JSNull | JSUndef | JSNumber | JSString
    | JSFun: list js_type_description -> js_type_description
    | JSObject: object_type_description -> js_type_description
and object_type_description: Type0 
  = | OTD: (string -> option property_descriptor) -> object_type_description
and property_descriptor: Type0
  = { configurable: bool
    ; vtype: js_type_description
    ; read:   (this: object_type_description) 
            -> (world: js_state)
            -> (js_state * object_type_description * js_type_description)
    ; write:  (this: object_type_description) 
            -> (world: js_state)
            -> (js_state * object_type_description * js_type_description)
    }
and js_state: Type0
  = count: nat & ((r:nat{r < count}) ^-> js_type_description)

new_effect JS = STATE_h js_state

assume new val globalThis: js_ref

let js_pre = st_pre_h js_state
let js_post a = st_post_h js_state a
let js_wp a = st_wp_h js_state a

unfold let lift_div_js (a:Type) (wp:pure_wp a) (p:js_post a) (h:js_state) = wp (fun a -> p a h)
sub_effect DIV ~> JS = lift_div_js

effect Js (a:Type) (pre:js_pre) (post: (js_state -> Tot (js_post a))) =
       JS a (fun (p:js_post a) (h:js_state) -> pre h /\ (forall a h1. (pre h /\ post h a h1) ==> p a h1))

effect Js' (a:Type) =
       Js a (fun _ -> True) (fun _ _ _ -> True)

open FStar.List.Tot

let (@@) (s: js_state) (r: js_ref) = 
  let (| count, s |) = s in
  let r = JsRef?.n r in
  if r < count then Some (s r) else None

let append (s: js_state) (t: js_type_description): js_ref * js_state
  = let (| count, s |) = s in
    let count' = count + 1 in
    let jsref = JsRef count in
    jsref, (| count', on (i: nat {i < count'}) (fun (i: nat {i < count'}) -> if i=count then t else s i) |)

val number_of_js_ref (r: js_ref)
  : JS int      (fun p s -> s @@ r == Some JSNumber /\ (forall x. p x s))
val bool_of_js_ref (r: js_ref)
  : JS bool   (fun p s -> s @@ r == Some JSBool   /\ (forall x. p x s))
val string_of_js_ref (r: js_ref)
  : JS string (fun p s -> s @@ r == Some JSString /\ (forall x. p x s))
val fn_n_of_js_ref (r: js_ref) (args: list js_ref)
  : JS js_ref (fun p s -> 
    match normalize_term (fold_left (fun acc x -> match acc, s @@ x with
                                             | Some l, Some x -> Some (x::l)
                                             | _ -> None) (Some []) args) with
    | Some args -> s @@ r == Some (JSFun args) /\ (forall x. p x s)
    | None -> False )

val read_property_of_js_ref (r: js_ref) (k: string)
  : JS string (fun p s -> match s @@ r with
                     | Some (JSObject (OTD f)) -> 
                            ( match f k with
                            | Some _ -> True /\ (forall x. p x s)
                            | _ -> False
                            )
                     | _ -> False
                     )

assume val access_js_property
  (#r: Type0) 
  (#p: prop_descr)
  ($o: object' p)
  (key: string {normalize (p key == Some r)})
  : Js' r



let op_Array_Access #r #p $o key = access_js_property #r #p o key

let pp: prop_descr = function 
    | "a" -> Some int
    | "b" -> Some int
    | "c" -> Some int
    | _ -> None

let x: object pp = admit ()

let xxx = assert (pp "a" == Some int)

let hello: int = x.("a")



module JS.Ast.Utils

open FStar.String
open FStar.List.Tot
open JS.Ast

// PR 2197 temp fix
module T = FStar.Tactics
let lookup_typ e n =
  T.print (">>>" ^ String.concat "." n);
  if mem (String.concat "." n) [
    "Prims.op_Addition"
  ; "Prims.op_Subtraction"
  ; "Prims.cps"
  ; "Prims.smt_theory_symbol"
  ; "Prims.range_0"
  ; "Prims.mk_range"
  ; "Prims.op_AmpAmp"
  ; "Prims.op_BarBar"
  ; "Prims.op_Negation"
  ; "Prims.op_Multiply"
  ; "Prims.op_Subtraction"
  ; "Prims.op_Addition"
  ; "Prims.op_Minus"
  ; "Prims.op_LessThanOrEqual"
  ; "Prims.op_GreaterThan"
  ; "Prims.op_GreaterThanOrEqual"
  ; "Prims.op_LessThan"
  ; "Prims.op_Equality"
  ; "Prims.op_disEquality"
  ; "Prims.strcat"
  ; "Prims._assume"
  ; "Prims.admit"
  ; "Prims.magic"
  ; "Prims.admitP"
  ; "Prims._assert"
  ; "Prims.cut"
  ; "Prims.op_Modulus"
  ; "Prims.op_Division"
  ; "Prims.string_of_bool"
  ; "Prims.string_of_int"
  ; "Prims.attribute"
  ; "Prims.hasEq"
  ; "Prims.eqtype"
  ; "Prims.bool"
  ; "Prims.c_False"
  ; "Prims.c_True"
  ; "Prims.unit"
  ; "Prims.squash"
  ; "Prims.logical"
  ; "Prims.equals"
  ; "Prims.eq2"
  ; "Prims.h_equals"
  ; "Prims.eq3"
  ; "Prims.b2t"
  ; "Prims.c_and"
  ; "Prims.l_and"
  ; "Prims.c_or"
  ; "Prims.l_or"
  ; "Prims.l_imp"
  ; "Prims.l_iff"
  ; "Prims.l_not"
  ; "Prims.l_ITE"
  ; "Prims.precedes"
  ; "Prims.has_type"
  ; "Prims.l_Forall"
  ; "Prims.prop"
  ; "Prims.range"
  ; "Prims.string"
  ; "Prims.guard_free"
  ; "Prims.dtuple2"
  ; "Prims.l_Exists"
  ; "Prims.int"
  ; "Prims.exn"
  ; "Prims.array"
  ; "Prims.list"
  ; "Prims.nat"
  ; "Prims.pos"
  ; "Prims.nonzero"
  ]
  then None
  else T.lookup_typ e n
// /PR fix

let sseq (l: list js_stmt): js_stmt
  = fold_left (fun acc h -> SSeq acc h) SNoOp l
  
let object = EVar (JSId None "Object")

let sFunction n args b = SFunction (JSFunction n args b)
let eFunction n args b = EFunction (JSFunction n args b)

let null = EConst CNull

let (===.) = EBinaryOp JsBin_Eq
let (&&.) = EBinaryOp JsBin_And

let wrap_as_expr (s: js_stmt)
  = let h s = EApp (EFunction (JSFunction None [] s)) [] in
    match s with
    | SReturn (EApp (EFunction (JSFunction None [] s')) []) -> h s'
    | _ -> h s

let rec replace_char_str (c r: string) (s: string)
  : Tot string (decreases (String.length s))
  = if String.length s > 0
    then let hd = String.sub s 0 1 in
         let tl = String.sub s 1 (String.length s - 1) in
         admitP (String.length tl = String.length s - 1);
         (if hd = c then r else hd) ^ replace_char_str c r tl
    else ""

let remove_tick = replace_char_str "'" "$tick$"

let name_of_jsid i = match i with
  | JSId _ n -> remove_tick n
  | ReservedId index -> "$"^string_of_int index
let range_of_jsid i = match i with | JSId r _ -> r | _ -> None
let idname (v: js_id) = EConst (CString (name_of_jsid v))

let str n = EConst (CString n)
let evar n = EVar (JSId None n)

let elet (vName: js_id) (value: js_expr) (body: js_expr) =
  wrap_as_expr ( SLet vName value `SSeq` (SReturn body) )

let elet' (vName: js_id) (value: js_expr) (body: js_expr) (counter: nat)
  : nat & js_expr
  = counter, elet vName value body

let elet_nonrec (vName: js_id) (value: js_expr) (body: js_expr) (counter: nat)
  : nat & js_expr
  = let counter = counter + 1 in
    counter, wrap_as_expr ( SLet (ReservedId counter) value `SSeq` SLet vName (EVar (ReservedId counter)) `SSeq` (SReturn body) )

open FStar.Tactics
let bv_to_js_id (bv: bv) r: js_id = JSId r (inspect_bv bv).bv_ppname
let fv_to_js_id (fv: fv) r: js_id = JSId r (String.concat "_" (inspect_fv fv))
let binder_to_js_id (b: binder) r: js_id = bv_to_js_id (fst (inspect_binder b)) r


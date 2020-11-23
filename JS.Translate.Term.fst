module JS.Translate.Term

open FStar.Tactics
open FStar.List.Tot
open JS.Ast
open JS.Ast.Utils
open JS.Translate.Helpers
open JS.Translate.Constructor
module O = Doc
open JS.Ast.DSL

let c_unit =
  { name = JSId None "Unit"
  ; args = []
  }

let vconst_to_js_ast (c: vconst) =
  match c with
  | C_Unit      -> mkCons c_unit []
  | C_Int     i -> EConst (CInt i)
  | C_True      -> EConst (CBool true)
  | C_False     -> EConst (CBool false)
  | C_String  s -> EConst (CString s)
  | C_Range   r -> EConst (CString "!RANGE!")
  | C_Reify     -> EConst (CString "!REIFY!")
  | C_Reflect _ -> EConst (CString "!REFLECT!")

let range_of_fv (fv: fv) = range_of_term (pack (Tv_FVar fv))
let range_of_bv (bv: bv) = range_of_term (pack (Tv_Var bv))
let range_of_binder (binder: binder) = range_of_term (binder_to_term binder)

let js_id_eq a b
    = match a, b with
    | JSId _ a, JSId _ b         -> a = b
    | ReservedId a, ReservedId b -> a = b
    | _ -> false

let rec branch_to_js_pattern_match (dico: constructor_dico) (pat: pattern): Tac _
  = match pat with
  | Pat_Constant vc -> JPat_Constant (vconst_to_js_ast vc)
  | Pat_Cons fv args -> 
         let name = fv_to_js_id fv (Some (Doc.range_to_range_info (range_of_fv fv))) in
         ( match find (fun c -> js_id_eq c.name name) dico with
         | Some c -> 
             JPat_Cons c
                       (Tactics.map (fun (a, _) -> branch_to_js_pattern_match dico a)
                       (admit (); args))
         | _ -> fail ("The constructor " ^ name_of_jsid name ^ " was not found in the supplied constructor dictionnary!" )
         )
  | Pat_Var bv | Pat_Wild bv | Pat_Dot_Term bv _ -> JPat_Var (bv_to_js_id bv (Some (Doc.range_to_range_info (range_of_bv bv))))

let rec term_to_js_ast' (dico: constructor_dico) (t: term) (count: nat)
  : Tac (nat & js_expr)
  = let recurse t count = term_to_js_ast' dico t count in
    let	r = Some (Doc.range_to_range_info (range_of_term t)) in
    match inspect t with
  | Tv_Var   v | Tv_BVar  v -> count, EVar (bv_to_js_id v r)
  | Tv_FVar  v -> count, EVar (fv_to_js_id v r)
  | Tv_App   hd (arg, aqual) -> 
    let count, hd = recurse hd count in
    let count, arg = recurse arg count in
    count, 
    ( match aqual with
    | Q_Explicit -> hd @@@ [arg]
    | _ -> make_implicit_app hd arg)
  | Tv_Abs   bv body -> 
    let count, body = recurse body count in
    let jid = binder_to_js_id bv r in
    ( match inspect_binder bv with
    | _, Q_Explicit -> count, EArrowFun [jid] body
    | _ -> make_implicit_abs jid body count
    )
  | Tv_Arrow _ _ | Tv_Type _ | Tv_Refine _ _ | Tv_AscribedT _ _ _ | Tv_AscribedC _ _ _ | Tv_Uvar  _ _ -> count, null
  | Tv_Const c -> count, vconst_to_js_ast c
  | Tv_Let rc _ bv def body -> 
    let count, body = recurse body count in
    let count, def = recurse def count in
    (if rc then elet' else elet_nonrec) (bv_to_js_id bv r) def body count
  | Tv_Unknown -> count, wrap_as_expr (SThrow (str "cannot translate Tv_Unknown"))
  | Tv_Match scrutinee brs -> 
             let count, branches = Tactics.fold_left (fun (count, l) (pat, body) -> 
                 let count, t = recurse body count in
                 count, l@[branch_to_js_pattern_match dico pat, t]
               ) (0,[]) brs in
             let count, scrutinee = recurse scrutinee count in
             js_of_patterns_match branches scrutinee count

let term_to_js_ast (dico: constructor_dico) (t: term)
  : Tac js_expr
  = snd (term_to_js_ast' dico t 0)



module JS.Translate

open FStar.Tactics
open FStar.List.Tot
open JS.Ast
open JS.Ast.Utils
module O = Doc
open JS.Translate.Constructor
open JS.Translate.Term
open JS.Translate.Helpers

let mk_js_constructor (n: name) (t: typ): Tac constructor
  = let bds, _ = collect_arr_bs t in
    { name = fv_to_js_id (pack_fv n) None
    ; args = Tactics.map (fun b -> 
           let _, q = inspect_binder b in
           ( match q with
           | (Q_Explicit, _) -> true
           | _ -> false
           ), JSId (Some (O.range_to_range_info (range_of_binder b))) (name_of_binder b)
      ) bds
    }

let js_of_sg_view_let (dico: constructor_dico) (sv: sigelt_view {Sg_Let? sv}) r: Tac (js_stmt)
  = let range = Some (Doc.range_to_range_info r) in
    let Sg_Let r fv _ _ def = sv in SLet (fv_to_js_id fv range) (term_to_js_ast dico def)

let is_constructor (name: name)
  = Cons? name &&
    ( let last = last name in
          String.length last > 0 && (
            let firstLetter = String.sub last 0 1 in
            String.uppercase firstLetter = firstLetter))

let inductive_name_from_constructor (n: name): Tac (list (name & typ))
  = if is_constructor n
    then [n, tc (top_env ()) (pack (Tv_FVar (pack_fv n)))]
    else []

let term_to_js_with_dep (t: term) (main_wrapper: js_expr -> js_stmt) (ignore_names: list name): Tac _
  = let names = name_closure (collect_names t) [] in
    let inductive_names = flatten (Tactics.map inductive_name_from_constructor names) in
    let sigelts': list (name & (sigelt_view & range)) = flatten (Tactics.map (fun n -> match lookup_typ (top_env ()) n with
      | Some se -> if mem n ignore_names then [] else [n, (inspect_sigelt se, range_of_sigelt se)]
      | None -> []
    ) names)
    in
    let sigelts: list (sigelt_view & range) = map snd sigelts' in
    let inductives = flatten (mapOption (function | Sg_Inductive _ _ _ _ c, r -> Some (map (fun c -> c, Some r) c) | _ -> None) sigelts) in
    // (match flatten (mapOption (fun (n, x) -> if Unk? x then Some n else None) sigelts) with
    // | [] -> ()
    // | l -> fail (String.concat ", " ([] @@ l))
    // );
    let dico = Tactics.map (fun ((n, t), r) -> mk_js_constructor n t) (inductives @ (map (fun c -> c, None) inductive_names)) in
    let lets = mapOption (fun (t: sigelt_view & _) -> let x, r = t in if Sg_Let? x then Some #((s: _ {Sg_Let? s})*_) (x,r) else None) sigelts in
    let lets_js = Tactics.map (fun (x, r) -> js_of_sg_view_let dico x r) lets in
    let inductives_js = map js_of_constructor dico in
    sseq (inductives_js @ lets_js @ [main_wrapper (term_to_js_ast dico t)])


module JS.Translate

open FStar.Tactics
open FStar.List.Tot
open JS.Ast
open JS.Ast.Utils
module O = Output
open JS.Translate.Constructor
open JS.Translate.Term
open JS.Translate.Helpers

let mk_js_constructor (n: name) (t: typ): Tac constructor
  = let bds, _ = collect_arr_bs t in
    { name = fv_to_js_id (pack_fv n)
    ; args = Tactics.map (fun b -> 
           let _, q = inspect_binder b in
           ( match q with
           | Q_Explicit -> true
           | _ -> false
           ), JSId (Some (O.range_to_range_info (range_of_binder b))) (name_of_binder b)
      ) bds
    }

let js_of_sg_view_let  (dico: constructor_dico) (se: sigelt_view {Sg_Let? se}): Tac (js_stmt)
  = let Sg_Let r fv _ _ def = se in SLet (fv_to_js_id fv) (term_to_js_ast dico def)

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
    let sigelts': list (name & sigelt_view) = flatten (Tactics.map (fun n -> match lookup_typ (top_env ()) n with
      | Some se -> if mem n ignore_names then [] else [n, inspect_sigelt se]
      | None -> []
    ) names)
    in
    let sigelts = map snd sigelts' in
    let inductives = flatten (mapOption (function | Sg_Inductive _ _ _ _ c -> Some c | _ -> None) sigelts) in
    // (match flatten (mapOption (fun (n, x) -> if Unk? x then Some n else None) sigelts) with
    // | [] -> ()
    // | l -> fail (String.concat ", " ([] @@ l))
    // );
    let dico = Tactics.map (fun (n, t) -> mk_js_constructor n t) (inductives @ inductive_names) in
    let lets = mapOption (fun (x: sigelt_view) -> if Sg_Let? x then Some #(s: _ {Sg_Let? s}) x else None) sigelts in
    let lets_js = Tactics.map (fun x -> js_of_sg_view_let dico x) lets in
    let inductives_js = map js_of_constructor dico in
    sseq (inductives_js @ lets_js @ [main_wrapper (term_to_js_ast dico t)])


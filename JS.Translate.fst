module JS.Translate

open FStar.Tactics
open FStar.List.Tot
open JS.Ast
open JS.Ast.Utils
module O = Doc
open JS.Translate.Constructor
open JS.Translate.Term
open JS.Translate.Helpers

irreducible let replace_top_level_with_js (x: js_expr) = ()

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

let extract_attr_replace (attr: term): Tac (option js_expr)
  = let head, args = collect_app attr in
    match inspect head, args with
    | Tv_FVar v, [(arg,_)] -> 
      if fv_to_string v = (`%replace_top_level_with_js)
      then Some (try_with
                   (fun _ -> unquote #js_expr arg)
                   (fun _ -> fail ("Could not extract a js_expr out of term '" ^ term_to_string arg ^ "'"))
                )
      else None
    | _ -> None

let rec extract_attr_replace_of_list (attrs: list term): Tac (option js_expr)
  = match attrs with
  | [] -> None
  | hd::tl -> ( match extract_attr_replace hd with
            | Some v -> Some v
            | _ -> extract_attr_replace_of_list tl
            )

let js_of_sg_view_let (dico: constructor_dico) (sv: sigelt_view {Sg_Let? sv}) (se: sigelt) r: Tac (js_stmt)
  = let range = Some (Doc.range_to_range_info r) in
    let Sg_Let r fv _ _ def = sv in 
    SLet (fv_to_js_id fv range)
         ( match extract_attr_replace_of_list (sigelt_attrs se) with
         | None    -> term_to_js_ast dico def
         | Some js -> js)

let isUpperCaseLetter = function
  |"A"|"B"|"C"|"D"|"E"|"F"|"G"|"H"|"I"|"J"|"K"
  |"L"|"M"|"N"|"O"|"P"|"Q"|"R"|"S"|"T"|"U"|"V"
  |"W"|"X"|"Y"|"Z" -> true | _ -> false

let is_constructor (name: name)
  = Cons? name &&
    ( let last = last name in
          String.length last > 0 && (
            let firstLetter = String.sub last 0 1 in
            isUpperCaseLetter firstLetter
              // String.uppercase firstLetter = firstLetter
            ))

let inductive_name_from_constructor (n: name): Tac (list (name & typ))
  = if is_constructor n
    then [n, tc (top_env ()) (pack (Tv_FVar (pack_fv n)))]
    else []

type test = {
     hey : int
  }

let _ = __proj__Mktest__item__hey

let n = ["JS";"Translate";"__proj__Mktest__item__hey"]

let _ = run_tactic (fun _ -> 
  let x = inductive_name_from_constructor ["JS";"Translate";"__proj__Mktest__item__hey"] in
  let x = map (fun (x,_) -> String.concat "." x) x in
  print (String.concat " ; " x)
) 

let fst3 (x,_,_) = x
let snd3 (_,x,_) = x
let thd3 (_,_,x) = x

let fstsnd3 (x,y,_) = (x,y)

let term_to_js_with_dep (t: term) (main_wrapper: js_expr -> js_stmt) (ignore_names: list name): Tac _
  = let names = name_closure (collect_names t) [] in
    let inductive_names = flatten (Tactics.map inductive_name_from_constructor names) in
    let sigelts': list (name & (sigelt_view & range & sigelt)) = flatten (Tactics.map (fun n -> match lookup_typ (top_env ()) n with
      | Some se -> if mem n ignore_names then [] else [n, (inspect_sigelt se, range_of_sigelt se, se)]
      | None -> []
    ) names)
    in
    let sigelts: list (sigelt_view & range & sigelt) = map snd sigelts' in
    let inductives = flatten (mapOption (function | Sg_Inductive _ _ _ _ c, r -> Some (map (fun c -> c, Some r) c) | _ -> None) (map fstsnd3 sigelts)) in
    // (match flatten (mapOption (fun (n, x) -> if Unk? x then Some n else None) sigelts) with
    // | [] -> ()
    // | l -> fail (String.concat ", " ([] @@ l))
    // );
    let dico = Tactics.map (fun ((n, t), r) -> mk_js_constructor n t) (inductives @ (map (fun c -> c, None) inductive_names)) in
    let lets = mapOption (fun (t: sigelt_view & _ & _) -> let x, r, y = t in if Sg_Let? x then Some #((s: _ {Sg_Let? s})*_*_) (x,r,y) else None) sigelts in
    let lets_js = Tactics.map (fun (x, r, y) -> js_of_sg_view_let dico x y r) lets in
    let inductives_js = map js_of_constructor dico in
    sseq (inductives_js @ lets_js @ [main_wrapper (term_to_js_ast dico t)])


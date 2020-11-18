module JS.Translate

open FStar.List.Tot
open JS.Ast
open JS.Ast.Utils

type constructor
  = { name: js_id
    ; args: list (bool & js_id)
    }
type constructor_dico = list constructor
    
let mkCons (c: constructor) (args: list js_expr): js_expr
  = ENew (EVar c.name) args

let instanceOfCons (v: js_expr) (c: constructor): js_expr
  = EBinaryOp JsBin_InstanceOf v (EGet (EVar c.name) (str "t"))

let enable_optional_implicit = false

let make_implicit_abs v (body: js_expr) (count: nat): nat & js_expr =
  if enable_optional_implicit
  then begin
  let count = count + 1 in
  // let  = ReservedId count in
  // let count = count + 1 in
  let bodyHolder = ReservedId count in
  count,
  EApp (eFunction None [] (
    sseq
      [ SLet v null
      ; SLet bodyHolder body
      ; SAssign (EGet (EVar bodyHolder) (str "feedImplicit")) (eFunction None [v] (
                // TODO: here body is duplicated, we could circumvent
                // this by having a binding `bodyHolder = v => body v`
                // However, we should NOT set a new value to `v`
                SReturn body
        ))
      ; SReturn (EVar bodyHolder)
      ]
  )) null []
  end else count, (eFunction None [v] (SReturn body))

let make_implicit_app f implicit_arg: js_expr
  = if enable_optional_implicit
    then
    let feedImplicit = EGet f (str "feedImplicit") in
    EApp (EBinaryOp JsBin_Or feedImplicit f) null [implicit_arg]
    else EApp f null [implicit_arg]

let js_of_constructor (c: constructor)
  = let thisCons = sFunction (Some c.name) (map snd c.args) (
        let assign_arg (arg: js_id) = ( (EConst CThis `EGet` idname arg) `SAssign` EVar arg) in
         sseq (map assign_arg (map snd c.args))
      ) in
    let mk_e body (explicit, arg) = 
      if explicit then eFunction None [arg] (SReturn body)
      else snd (make_implicit_abs arg body 0)
    in
    let mk_curried args body = fold_left mk_e body (rev args) in
    let creatorLet = JSId None "creator" in
    let creator = mk_curried c.args (
      ENew (EVar c.name) (map EVar (map snd c.args))
    ) in
    SLet c.name (wrap_as_expr (
       sseq
         [ thisCons
         ; SLet creatorLet creator
         ; SAssign (EGet (EVar creatorLet) (str "t")) (EVar c.name)
         ; SReturn (EVar creatorLet)
         ]
    ))

type pattern_match =
    | JPat_Constant : js_expr -> pattern_match
    | JPat_Cons     : constructor -> list pattern_match -> pattern_match
    | JPat_Var      : js_id -> pattern_match

let rec zip (a: list 'a) (b: list 'b) =
  match a, b with
  | a_hd::a_tl, b_hd::b_tl -> (a_hd,b_hd)::zip a_tl b_tl
  | _ -> []
  
let rec js_condition_of_pattern_match (p: pattern_match) (head: js_expr)
  = match p with
  | JPat_Constant e -> head ===. e
  | JPat_Cons cons args -> fold_left (fun acc (pat, name) -> acc &&. js_condition_of_pattern_match pat (admit (); (EGet head (idname name))))
                                    (head `instanceOfCons` cons)
                                    (zip args (map snd cons.args))
  | JPat_Var _ -> EConst (CBool true)

let rec js_bindings_of_pattern_match (p: pattern_match) (head: js_expr)
  : list (js_id * js_expr)
  = match p with
  | JPat_Constant e -> []
  | JPat_Cons cons args -> fold_left (fun acc (pat, name) -> acc @ js_bindings_of_pattern_match pat (admit (); (EGet head (idname name))))
                                    []
                                    (zip args (map snd cons.args))
  | JPat_Var v -> [(v, head)]

let js_of_pattern_match (p: pattern_match) (head: js_expr) (body: js_expr)
  = let cond = js_condition_of_pattern_match p head in
    let bindings = js_bindings_of_pattern_match p head in
    let letClauses = fold_left (fun p (v, e) -> if p = SNoOp then SLet v e else p `SSeq` SLet v e) SNoOp bindings in
    let body = letClauses `SSeq` SReturn body in
    SIf cond body None


let js_of_patterns_match (pb: list (pattern_match * js_expr)) (head: js_expr) (counter: nat)
  : nat * js_expr
  = let counter = counter + 1 in
    counter,
    wrap_as_expr begin
      let let_temp = SLet (ReservedId counter) head in
      let head = EVar (ReservedId counter) in
      let branches = map (fun (pat, body) -> js_of_pattern_match pat head body) pb in
      let_temp      `SSeq`
      sseq branches `SSeq`
      SThrow (
        EBinaryOp JsBin_Plus
          (str "Failed to pattern match ")
          (head `EGet` str "constructor" `EGet` str "name")
      )
    end
















let c_unit =
  { name = JSId None "Unit"
  ; args = []
  }

open FStar.Tactics
open FStar.List.Tot
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



let rec branch_to_js_pattern_match (dico: constructor_dico) (pat: pattern)
  : Tac _
  =
  match pat with
  | Pat_Constant vc -> JPat_Constant (vconst_to_js_ast vc)
  | Pat_Cons fv args -> 
         let name = fv_to_js_id fv in
         ( match find (fun c -> c.name=name) dico with
         | Some c -> 
             JPat_Cons c
                       (Tactics.map (fun (a, _) -> branch_to_js_pattern_match dico a)
                       (admit (); args))
         | _ -> fail ("The constructor " ^ name_of_jsid name ^ " was not found in the supplied constructor dictionnary!" )
         )
  | Pat_Var bv | Pat_Wild bv | Pat_Dot_Term bv _ -> JPat_Var (bv_to_js_id bv)

let rec term_to_js_ast' (dico: constructor_dico) (t: term) (count: nat)
  : Tac (nat & js_expr)
  = let recurse t count = term_to_js_ast' dico t count in
    match inspect t with
  | Tv_Var   v | Tv_BVar  v -> count, EVar (bv_to_js_id v)
  | Tv_FVar  v -> count, EVar (fv_to_js_id v)
  | Tv_App   hd (arg, aqual) -> 
    let count, hd = recurse hd count in
    let count, arg = recurse arg count in
    count, 
    ( match aqual with
    | Q_Explicit -> EApp hd null [arg]
    | _ -> make_implicit_app hd arg)
  | Tv_Abs   bv body -> 
    let count, body = recurse body count in
    let jid = binder_to_js_id bv in
    ( match inspect_binder bv with
    | _, Q_Explicit -> count, EAbs [jid] body
    | _ -> make_implicit_abs jid body count
    )
  | Tv_Arrow _ _ | Tv_Type _ | Tv_Refine _ _ | Tv_AscribedT _ _ _ | Tv_AscribedC _ _ _ | Tv_Uvar  _ _ -> count, null
  | Tv_Const c -> count, vconst_to_js_ast c
  | Tv_Let r _ bv def body -> 
    let count, body = recurse body count in
    let count, def = recurse def count in
    (if r then elet' else elet_nonrec) (bv_to_js_id bv) def body count
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



























let constructor_names_of_sigelt (se: sigelt): Tac (list (name & typ))
  = match inspect_sigelt se with
  | Sg_Inductive _ _ _ _ cts -> cts
  | _ -> fail "sigelt not an inductive" 


let constructor_names_of_type_name (n: name): Tac (list (name & typ))
  = match lookup_typ (top_env ()) n with
  | Some n -> constructor_names_of_sigelt n
  | _ -> fail "name not found"

let mk_js_constructor (n: name) (t: typ)
  : Tac constructor
  = let bds, _ = collect_arr_bs t in
    { name = fv_to_js_id (pack_fv n)
    ; args = map (fun b -> 
           let _, q = inspect_binder b in
           ( match q with
           | Q_Explicit -> true
           | _ -> false
           ), JSId None (name_of_binder b)
      ) bds
    }

let mk_js_constructors (l: list (name & typ))
  : Tac (list constructor)
  = Tactics.map (fun (n, t) -> mk_js_constructor n t) l 

let constructors_of_type_names (n: list name): Tac (list constructor)
  = flatten (Tactics.map mk_js_constructors (Tactics.map constructor_names_of_type_name n))

let js_of_sg_view_let  (dico: constructor_dico) (se: sigelt_view {Sg_Let? se}): Tac (js_stmt)
  = let Sg_Let r fv _ _ def = se in SLet (fv_to_js_id fv) (term_to_js_ast dico def)


let rec (@@) (#a: eqtype) (l1 l2: list a): Tot (list a) (decreases l2) = 
  match l2 with | [] -> l1
                | hd::tl -> if mem hd l1 then l1 @@ tl
                          else (hd::l1) @@ tl


let rec collect_names (t: term)
  : Tac (list name)
  = match inspect t with
  | Tv_FVar  v -> [inspect_fv v]
  | Tv_App   hd (arg, _) -> collect_names hd @@ collect_names arg
  | Tv_Abs   _ body -> collect_names body
  | Tv_Let _ _ _ def body -> collect_names def @@ collect_names body
  | Tv_Arrow _ _ | Tv_Type _ | Tv_Refine _ _ | Tv_AscribedT _ _ _ | Tv_AscribedC _ _ _ | Tv_Uvar _ _ | Tv_Var _ | Tv_BVar _ | Tv_Const _ | Tv_Unknown -> []
  | Tv_Match scrutinee brs -> Tactics.fold_left (fun l b -> l @@ collect_names_of_branch b) (collect_names scrutinee) brs
and collect_names_of_branch (b: branch)
  : Tac (list name)
  = let pat, body = b in
    collect_names body @@ collect_names_of_pat pat
and collect_names_of_pat (p: pattern)
  : Tac (list name)
  = match p with
  | Pat_Cons fv l -> inspect_fv fv::(flatten (Tactics.map collect_names_of_pat (map fst l)))
  | _ -> []

let names_of_name (n: name): Tac (list name) 
  = 
  match lookup_typ (top_env ()) n with
  | Some f -> (match inspect_sigelt f with
           | Sg_Let _ _ _ _ d -> collect_names d
           | _ -> [])
  | None -> []

let rec name_closure (names_todo: list name) (exclude: list name)
  : Tac (list name)
  = let excluded someName exclude = mem someName exclude in 
    match names_todo with | [] -> []
  | n::todo -> if excluded n exclude
             then name_closure todo exclude
             else let newTodo = names_of_name n in
                  n :: name_closure (todo @@ newTodo) (n::exclude)






let rec mfilter (f: 'a -> option 'b) (l: list 'a): list 'b
  = match l with
  | [] -> []
  | hd::tl -> let r = mfilter f tl in match f hd with | Some v -> v::r | _ -> r

let is_constructor (name: name)
  = Cons? name &&
    ( let last = last name in
          String.length last > 0 && (
            let firstLetter = String.sub last 0 1 in
            String.uppercase firstLetter = firstLetter))

let inductive_name_from_constructor (n: name)
  : Tac (list (name & typ))
  = print ("--> " ^ implode_qn n ^ " : " ^ string_of_bool (is_constructor n));
    if is_constructor n
    then [n, tc (top_env ()) (pack (Tv_FVar (pack_fv n)))]
    else []
    // let _, comp = collect_arr (tc (top_env ()) (pack (Tv_FVar (pack_fv n)))) in
    // match inspect_comp comp with
    // | C_Total ret _ -> 
    //   let x,_   = collect_app
    //   begin match lookup_typ (top_env ()) n with
    //     | Some se -> begin match inspect_sigelt se with
    //                     | Sg_Inductive n _ _ _ c -> [n]
    //                     | _ -> print ("inductive_name_from_constructor("^implode_qn n^"): not a Sg_Inductive"); []
    //                 end
    //     | _ -> print ("inductive_name_from_constructor("^implode_qn n^"): cannot lookup the name"); []
    //   end else []
    // | _ -> print ("inductive_name_from_constructor("^implode_qn n^"): comp not total"); []

let term_to_js_with_dep (t: term) (main_wrapper: js_expr -> js_stmt) (ignore_names: list name): Tac _
  = let names = name_closure (collect_names t) [] in
    let namesxx = flatten (Tactics.map inductive_name_from_constructor names) in
    let sigelts': list (name & sigelt_view) = flatten (Tactics.map (fun n -> match lookup_typ (top_env ()) n with
      | Some se -> if mem n ignore_names then [] else [n, inspect_sigelt se]
      | None -> []
    ) names)
    in
    // let sigeltsX = map (fun (n, se) -> 
    //     match se with
    //     | Sg_Let -> 
    //     if is_constructor n
    //     then 
    //   ) sigelts' in
    let sigelts = map snd sigelts' in
    let inductives = flatten (mfilter (function | Sg_Inductive _ _ _ _ c -> Some c | _ -> None) sigelts) in
    // (match flatten (mfilter (fun (n, x) -> if Unk? x then Some n else None) sigelts) with
    // | [] -> ()
    // | l -> fail (String.concat ", " ([] @@ l))
    // );
    let dico: constructor_dico = mk_js_constructors (inductives @ namesxx) in
    let lets = mfilter (fun (x: sigelt_view) -> if Sg_Let? x then Some #(s: _ {Sg_Let? s}) x else None) sigelts in
    let lets_js = Tactics.map (fun x -> js_of_sg_view_let dico x) lets in
    let inductives_js = map js_of_constructor dico in
    sseq (inductives_js @ lets_js @ [main_wrapper (term_to_js_ast dico t)])




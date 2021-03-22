module JS.Translate.Helpers

open FStar.Tactics
open FStar.List.Tot
open JS.Ast
open JS.Ast.Utils
module O = Doc


(*** Optionnal implicit support ***)
/// If `enable_optional_implicit` is set to false, implicit and
/// explicit binders in abstractions are treated the same. This should
/// be the case: F* typechecker should always "fill the holes" of
/// implicits, i.e. no implicit should be left
/// uninstantiated. However, if you skip F* typecheck phase, you end
/// up with term such as: `(fun #x y -> something) 3`, that is, with
/// applications that "misses" implicits. The
/// `enable_optional_implicit` flag makes the JS backend use a trick
/// to skip the implicit that were left uninstantiated.
let enable_optional_implicit = false
let make_implicit_abs v (body: js_expr) (count: nat): nat & js_expr =
  if enable_optional_implicit
  then begin
  let count = count + 1 in
  // let  = ReservedId count in
  // let count = count + 1 in
  let bodyHolder = ReservedId count in
  count,
  JS.Ast.DSL.(
    EApp (eFunction None [] (
      sseq
        [ SLet v null
        ; SLet bodyHolder body
        ; SAssign ((EVar bodyHolder).(str "feedImplicit")) (eFunction None [v] (
                  // TODO: here body is duplicated, we could circumvent
                  // this by having a binding `bodyHolder = v => body v`
                  // However, we should NOT set a new value to `v`
                  SReturn body
          ))
        ; SReturn (EVar bodyHolder)
        ]
    )) []
  )
  end else count, (eFunction None [v] (SReturn body))

let make_implicit_app f implicit_arg: js_expr
  = if enable_optional_implicit
    then
    JS.Ast.DSL.(
      EApp (JS.Ast.DSL.(f.(str "feedImplicit")) ||. f) [implicit_arg]
    )
    else EApp f [implicit_arg]

(*** Miscelanous helpers ***)

let rec zip (a: list 'a) (b: list 'b) =
  match a, b with
  | a_hd::a_tl, b_hd::b_tl -> (a_hd,b_hd)::zip a_tl b_tl
  | _ -> []

let rec (@@) (#a: eqtype) (l1 l2: list a): Tot (list a) (decreases l2) = 
  match l2 with | [] -> l1
                | hd::tl -> if mem hd l1 then l1 @@ tl
                          else (hd::l1) @@ tl

let rec mapOption (f: 'a -> option 'b) (l: list 'a): list 'b
  = match l with
  | [] -> []
  | hd::tl -> let r = mapOption f tl in match f hd with | Some v -> v::r | _ -> r

let range_of_binder b: Tac range = range_of_term (binder_to_term b)

(*** Names collection ***)
/// The following just browse terms and collect any free
/// variable. Note that types are irrelevant and thus discarded.
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

let temp_fix_pr2197 (n: name): bool
  = false

/// Given a toplevel name, `names_of_name` inspect the toplevel and
/// returns a list of the names it directly use.
let names_of_name (n: name): Tac (list name) 
  = match lookup_typ (top_env ()) n with
  | Some f -> (match inspect_sigelt f with
           | Sg_Let _ _ _ _ d -> collect_names d
           | _ -> [])
  | None -> []

/// `name_closure` computes a list of every names present directly or
/// indirectly in the given toplevels.
let rec name_closure (names_todo: list name) (exclude: list name)
  : Tac (list name)
  = let excluded someName exclude = mem someName exclude in 
    match names_todo with | [] -> []
  | n::todo -> if excluded n exclude
             then name_closure todo exclude
             else let newTodo = names_of_name n in
                  n :: name_closure (todo @@ newTodo) (n::exclude)


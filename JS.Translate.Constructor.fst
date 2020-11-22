module JS.Translate.Constructor

open FStar.List.Tot
open JS.Ast
open JS.Ast.Utils
open JS.Translate.Helpers
module O = Output
open JS.Ast.DSL

type constructor
  = { name: js_id
    ; args: list (bool & js_id)
    }
type constructor_dico = list constructor
    
let mkCons (c: constructor) (args: list js_expr): js_expr
  = EVar c.name `new_` args

let instanceOfCons (v: js_expr) (c: constructor): js_expr
  = v `instanceof` (EVar c.name).(str "t")

let js_of_constructor (c: constructor)
  = let thisCons = sFunction (Some c.name) (map snd c.args) (
        let assign_arg (arg: js_id) = (this.(idname arg) <-. EVar arg) in
         sseq (map assign_arg (map snd c.args))
      ) in
    let mk_e body (explicit, arg) = 
      if explicit then eFunction None [arg] (SReturn body)
      else snd (make_implicit_abs arg body 0)
    in
    let mk_curried args body = fold_left mk_e body (rev args) in
    let creatorLet = JSId None "creator" in
    let creator = mk_curried c.args (
      EVar c.name `new_` map EVar (map snd c.args)
    ) in
    SLet c.name (wrap_as_expr (
       sseq
         [ thisCons
         ; SLet creatorLet creator
         ; SAssign ((EVar creatorLet).(str "t")) (EVar c.name)
         ; SReturn (EVar creatorLet)
         ]
    ))

type pattern_match =
    | JPat_Constant : js_expr -> pattern_match
    | JPat_Cons     : constructor -> list pattern_match -> pattern_match
    | JPat_Var      : js_id -> pattern_match

let rec js_condition_of_pattern_match (p: pattern_match) (head: js_expr): Tot js_expr (decreases p)
  = match p with
  | JPat_Constant e -> head ===. e
  | JPat_Cons cons args -> fold_left (fun acc (pat, name) -> acc &&. js_condition_of_pattern_match (admit (); pat) (head.(idname name)))
                                    (head `instanceOfCons` cons)
                                    (zip args (map snd cons.args))
  | JPat_Var _ -> EConst (CBool true)

let rec js_bindings_of_pattern_match (p: pattern_match) (head: js_expr)
  : Tot (list (js_id * js_expr)) (decreases p)
  = match p with
  | JPat_Constant e -> []
  | JPat_Cons cons args -> fold_left (fun acc (pat, name) -> acc @ js_bindings_of_pattern_match (admit (); pat) (head.(idname name)))
                                    []
                                    (zip args (map snd cons.args))
  | JPat_Var v -> [(v, head)]

let js_of_pattern_match (p: pattern_match) (head: js_expr) (body: js_expr)
  = let cond = js_condition_of_pattern_match p head in
    let bindings = js_bindings_of_pattern_match p head in
    let letClauses = fold_left (fun p (v, e) -> if SNoOp? p then SLet v e else p `SSeq` SLet v e) SNoOp bindings in
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
          (head.(str "constructor").(str "name"))
      )
    end


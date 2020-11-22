module Output

open FStar.String
open FStar.List.Tot
module R = FStar.Reflection.Builtins
module RD = FStar.Reflection.Data

let rec smaller' #t p ref (l: list t {l << ref /\ for_all p l})
  : (r: list (x: t {x << ref /\ p x}) { length l == length r })
  = match l with
  | [] -> []
  | hd::tl -> hd::smaller' #t p ref tl

let rec smaller #t ref (l: list t {l << ref})
  : (r: list (x: t {x << ref}) { length l == length r })
  = match l with
  | [] -> []
  | hd::tl -> hd::smaller #t ref tl

type position = | Position: col:int -> line:int -> position
type range_info = | RangeInfo: file:string -> startp: position -> endp: position -> range_info

let range_to_range_info (r: range)
  = let max (x y: int) = if x > y then x else y in
    let h (t: int*int) = Position (max (fst t) 0) (max (snd t) 0) in
    let r = R.inspect_range r in
    RangeInfo r.RD.file_name (h r.RD.start_pos) (h r.RD.end_pos)

type doc (a: Type) =
  | DAnnotated: doc a -> a -> doc a
  | DString: string -> doc a
  | DIndent: d: doc a -> doc a
  | DConcat: doc a -> doc a -> doc a
  | DNewLine | DEmpty

let annote #a: doc a -> a -> doc a = DAnnotated
let str #a: string -> doc a = DString
let (<+>) #a: doc a -> doc a -> doc a = DConcat
let nl #a: doc a = DNewLine
let empty #a: doc a = DEmpty
let indent #a: doc a -> doc a = DIndent
let concat #a: list (doc a) -> doc a = function
  | [] -> empty
  | hd::tl -> fold_left (<+>) hd tl
let s = str " "

let lparen = str "("
let rparen = str ")"
let lbrace = str "{"
let rbrace = str "}"

let semicolon = str ";"
let klet      = str "let"
let kequal    = str "="
let comma     = str ","
let dot       = str "."


let rec prependToAll sep
  = function | [] -> [] | hd::tl -> sep::hd::prependToAll sep tl
 
let intersperse sep
  = function | [] -> [] | a::tl -> a::prependToAll sep tl
  
let concatSep #a (sep:doc a) (l:list (doc a)): doc a
  = concat (intersperse sep l)

type atom = | AStr: string -> atom | ANewLine
type flat_annot a = | Annot : pstart:int -> pend:int -> body:a -> flat_annot a
type flat_doc a = list atom * list (flat_annot a)

let max x y = if x > y then x else y
let max_offset_list (l: list 'a) = max 0 (length l - 1)
let offset n (Annot s e a) = Annot (s+n) (s+e) a

let rec flatten_doc #a (d: doc a): flat_doc a
  = match d with
  | DAnnotated doc annot -> let l, ann = flatten_doc doc in
                           l, Annot 0 (max_offset_list l) annot::ann
  | DString str -> [AStr str], []
  | DIndent idoc ->  
           let ident = " " in
           let fdoc, fan = flatten_doc idoc in
           let fdoc = flatten (map (function | ANewLine -> [ANewLine;AStr ident] | AStr s -> [AStr s]) fdoc) in
           fdoc, fan
  | DConcat d1 d2 -> 
    let fd1, a1 = flatten_doc d1 in
    let fd2, a2 = flatten_doc d2 in
    let len = length fd1 in
    fd1 @ fd2, a1 @ map (offset len) a2
  | DNewLine -> [ANewLine], []
  | DEmpty -> [], []

let flat_doc_to_string (fd: flat_doc _): string
  = String.concat "" (map (function | AStr s -> s | ANewLine -> "\n") (fst fd))

let rec zip (a: list 'a) (b: list 'b) =
  match a, b with
  | a_hd::a_tl, b_hd::b_tl -> (a_hd,b_hd)::zip a_tl b_tl
  | _ -> []

let flat_doc_to_annotations (fd: flat_doc 'a): list (position * position * 'a)
  = let lookup_table = fold_left (fun (l, abs_pos) -> function
                                    | ANewLine -> (abs_pos::l, abs_pos+1)
                                    | AStr s -> (l, abs_pos + String.length s)
                                 ) ([], 0) (fst fd) in
    let lookup_table, rest = lookup_table in
    let lookup_table = mapi (fun i (s, e) -> i, s, e) (zip (0::lookup_table) (lookup_table@[rest])) in
    let lookup_table (x: int): position
      = match find (fun (i,s,e) -> x >= s && x<=e) lookup_table with
      | Some (i,s,e) -> (Position (s - x) i)
      | None -> Position (-1) (-1)
    in
    map (fun (Annot s e a) -> (lookup_table s, lookup_table e, a)) (snd fd)

let doc_to_string (d: doc 'a): string = flat_doc_to_string (flatten_doc d)
let doc_to_annotations (d: doc 'a): list (position * position * 'a)
  = flat_doc_to_annotations (flatten_doc d)


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

type position = | Position: col:nat -> line:nat -> position
type range_info = | RangeInfo: file:string -> startp: position -> endp: position -> range_info

let range_to_range_info (r: range)
  = let max (x y: int) = if x > y then x else y in
    let h (t: int*int) = Position (max (fst t) 0) (max (snd t) 0) in
    let r = R.inspect_range r in
    RangeInfo r.RD.file_name (h r.RD.start_pos) (h r.RD.end_pos)

type doc =
  | OPair: jump: bool -> left: string -> right: string -> content: list doc -> doc
  | OQuote: string -> doc
  | OIdentitier: source: option range_info -> name: string -> doc
  | OKeyword: spaced: bool -> keyword: string -> doc
  | OSeparatedList: separator:doc -> items: list doc -> doc
  | ONest: list doc -> doc
  | OEmpty
  
let rec string_of_doc' (tab: string) (o: doc): Tot _ (decreases o)
  = let map_self tab l = map (fun x -> string_of_doc' tab x) l in 
    match o with
  | OPair jump left right content -> 
          let nl0 = if jump then "\n" ^ tab else "" in
          let tab = if jump then tab ^ "  " else "" in
          let nl1 = if jump then "\n" ^ tab else "" in
          left ^ nl0 ^ (String.concat "" (map_self tab (smaller o content))) ^ nl1 ^ right 
  | OQuote content -> "\"" ^ content ^ "\""
  | OIdentitier _ name -> name
  | OKeyword spaced kwd -> let s = if spaced then " " else "" in
                          s ^ kwd ^ s
  | OSeparatedList sep items -> (String.concat (string_of_doc' tab sep) (map_self tab (smaller o items)))
  | ONest l -> String.concat "" (map_self tab (smaller o l))
  | OEmpty -> ""

let string_of_doc = string_of_doc' ""


let (<+>) (a b: doc) =
  


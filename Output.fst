module Output

open FStar.String
open FStar.List.Tot

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

type mrange = int * int * int

type output =
  | OPair: jump: bool -> left: string -> right: string -> content: list output -> output
  | OQuote: string -> output
  | OIdentitier: source: option mrange -> name: string -> output
  | OKeyword: spaced: bool -> keyword: string -> output
  | OSeparatedList: separator:output -> items: list output -> output
  | ONest: list output -> output
  | OEmpty
  
let rec string_of_output' (tab: string) (o: output): Tot _ (decreases o)
  = let map_self tab l = map (fun x -> string_of_output' tab x) l in 
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
  | OSeparatedList sep items -> (String.concat (string_of_output' tab sep) (map_self tab (smaller o items)))
  | ONest l -> String.concat "" (map_self tab (smaller o l))
  | OEmpty -> ""

let string_of_output = string_of_output' ""



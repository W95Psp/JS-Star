module Output

open FStar.String
open FStar.List.Tot

type mrange = int * int * int

type output =
  | OPair: jump: bool -> left: string -> right: string -> content: list output -> output
  | OQuote: string -> output
  | OIdentitier: source: option mrange -> name: string -> output
  | OKeyword: spaced: bool -> keyword: string -> output
  | OSeparatedList: separator:output -> items: list output -> output
  | ONest: list output -> output
  | OEmpty

let rec string_of_output' (tab: string) (o: output)
  = let map_self tab (l: list output) = map (fun x -> admit (); string_of_output' tab x) (admit (); l) in 
    match o with
  | OPair jump left right content -> 
          let nl0 = if jump then "\n" ^ tab else "" in
          let tab = if jump then tab ^ "  " else "" in
          let nl1 = if jump then "\n" ^ tab else "" in
          left ^ nl0 ^ (String.concat "" (map_self tab content)) ^ nl1 ^ right 
  | OQuote content -> "\"" ^ content ^ "\""
  | OIdentitier _ name -> name
  | OKeyword spaced kwd -> let s = if spaced then " " else "" in
                          s ^ kwd ^ s
  | OSeparatedList sep items -> (String.concat (string_of_output' tab sep) (map_self tab items))
  | ONest l -> String.concat "" (map_self tab l)
  | OEmpty -> ""

let string_of_output = string_of_output' ""



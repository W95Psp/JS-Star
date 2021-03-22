# JS*

This repository provides F* meta-programs that transpile on the fly F* terms to javascript terms, using the F* normalizer.

## Usability
I've tested it for a few programs, that works fairly nicely!

 - [ ] Sourcemaps
   + this is almost done already
 - [ ] JS FFI
   - [ ] JS effect to interact with JS's world
   - [ ] DOM modelization
   - [ ] Adapt [F* TODO webapp](http://raw.githack.com/W95Psp/FStar-HTTP-Server/master/todo-app.html) so that it works with this repo
 - [ ] add `nix` build

## Example

For instance the following module transpiles `main` and write it to the file ""example.js":

```fstar
module Example

open FStar.Tactics
open FStar.List.Tot
open JS
open JS.Ast
open JS.Ast.DSL

let rec factorial (n:nat) = 
  let open FStar.Mul in
  if n = 0 then 1 else n * (factorial (n - 1))

let rec fibonacci n =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

let main n = 
  [ ("fibonacci(" ^ string_of_int n ^ ") => " ^ string_of_int (fibonacci n))
  ; ("factorial(" ^ string_of_int n ^ ") => " ^ string_of_int (factorial n))
  ]

let _ = run_tactic (fun _ -> 
  term_to_js_files "example" (fun e -> console_log (e @@@ [EConst (CInt 5)])
                         )
                         (`main)
)
```

Running `node example.js` gives the following output:
```javascript
Prims_Cons {
  a: 'Type:STRING',
  hd: 'fibonacci5 => 8',
  tl: Prims_Cons {
    a: 'Type:STRING',
    hd: 'factorial5 => 120',
    tl: Prims_Nil { a: 'Type:STRING' }
  }
}
```




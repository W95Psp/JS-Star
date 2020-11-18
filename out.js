 let Prims_int = "Type:INT"; let Prims_nat = "Type:NAT"; let Prims_op_Addition = ( function (x){
 return ( function (y){
 return (x + y);
  });
  }); let Prims_op_Subtraction = ( function (x){
 return ( function (y){
 return (x - y);
  });
  }); let Prims_op_Equality = ( function (tvar){
 return ( function (x){
 return ( function (y){
 return (x === y);
  });
  });
  }); let Prims_op_LessThanOrEqual = ( function (x){
 return ( function (y){
 return (x <= y);
  });
  }); let Prims_Cons = (( function (){
 function Prims_Cons(a , hd , tl){
   this ["a"] = a; this ["hd"] = hd; this ["tl"] = tl;
    } let creator = ( function (a){
 return ( function (hd){
 return ( function (tl){
 return ( new Prims_Cons(a , hd , tl));
  });
  });
  });creator["t"] = Prims_Cons; return creator;
  })()); let Prims_Nil = (( function (){
 function Prims_Nil(a){
   this ["a"] = a;
    } let creator = ( function (a){
 return ( new Prims_Nil(a));
  });creator["t"] = Prims_Nil; return creator;
  })()); let Main_hey = ((n) => ((Prims_op_Addition((Main_sum((Main_test( 4 ))))))((((((FStar_List_Tot_Base_fold_left(Prims_int))(Prims_int))(((y) => ((x) => ((Prims_op_Addition(y))(x))))))( 0 ))((Main_test( 4 ))))))); let Main_test = ((n) => (( function (){
 let $2 = (Main_f(n)); let t = $2; return (( function (){
 let $1 = ((Prims_op_LessThanOrEqual(n))( 0 )); if (($1 ===  true )){
   return (((Prims_Cons(Prims_int))(t))((Prims_Nil(Prims_int))));
    } if ( true ){
   let uu___ = $1; return (((Prims_Cons(Prims_int))(t))((Main_test(((Prims_op_Subtraction(n))( 1 ))))));
    } throw ("Failed to pattern match " + $1["constructor"]["name"]);
  })());
  })())); let Main_f = ((x) => (( function (){
 let $1 = ((Prims_op_LessThanOrEqual(x))( 0 )); if (($1 ===  true )){
   return  0 ;
    } if ( true ){
   let uu___ = $1; return ((Prims_op_Addition(x))((Main_f(((Prims_op_Subtraction(x))( 1 ))))));
    } throw ("Failed to pattern match " + $1["constructor"]["name"]);
  })())); let Main_sum = ((l) => (( function (){
 let $1 = l; if ((($1 instanceof Prims_Nil["t"]) &&  true )){
   let uu___ = $1["a"]; return  0 ;
    } if ((((($1 instanceof Prims_Cons["t"]) &&  true ) &&  true ) &&  true )){
   let uu___ = $1["a"]; let hd = $1["hd"]; let tl = $1["tl"]; return ((Prims_op_Addition(hd))((Main_sum(tl))));
    } throw ("Failed to pattern match " + $1["constructor"]["name"]);
  })())); let FStar_List_Tot_Base_fold_left = ( function ($tick$a){
 return ( function ($tick$b){
 return ((f) => ((x) => ((l) => (( function (){
 let $1 = l; if ((($1 instanceof Prims_Nil["t"]) &&  true )){
   let uu___ = $1["a"]; return x;
    } if ((((($1 instanceof Prims_Cons["t"]) &&  true ) &&  true ) &&  true )){
   let uu___ = $1["a"]; let hd = $1["hd"]; let tl = $1["tl"]; return (((((FStar_List_Tot_Base_fold_left($tick$a))($tick$b))(f))(((f(x))(hd))))(tl));
    } throw ("Failed to pattern match " + $1["constructor"]["name"]);
  })()))));
  });
  });(console["log"]((Main_hey( 5 ))));
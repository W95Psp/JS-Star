let Prims_int='Type:INT';
let Prims_nat='Type:NAT';
let Prims_string='Type:STRING';
let Prims_op_Addition=(function (x){
 return (function (y){
  return (x+y);
  
 });
 
});
let Prims_op_Multiply=(function (x){
 return (function (y){
  return (x*y);
  
 });
 
});
let FStar_Mul_op_Star=(function (x){
 return (function (y){
  return (x*y);
  
 });
 
});
let Prims_op_Subtraction=(function (x){
 return (function (y){
  return (x-y);
  
 });
 
});
let Prims_op_Equality=(function (tvar){
 return (function (x){
  return (function (y){
   return (x===y);
   
  });
  
 });
 
});
let Prims_op_LessThanOrEqual=(function (x){
 return (function (y){
  return (x<=y);
  
 });
 
});
let Prims_string_of_int=(function (s){
 return (''+s);
 
});
let Prims_op_Hat=(function (x){
 return (function (y){
  return (x+y);
  
 });
 
});
let Prims_Cons=((function (){
 function Prims_Cons(a,hd,tl){
  (this['a'])=a;
  (this['hd'])=hd;
  (this['tl'])=tl;
  
 }let creator=(function (a){
  return (function (hd){
   return (function (tl){
    return (new Prims_Cons(a,hd,tl));
    
   });
   
  });
  
 });
 (creator['t'])=Prims_Cons;
 return creator;
 
})());
let Prims_Nil=((function (){
 function Prims_Nil(a){
  (this['a'])=a;
  
 }let creator=(function (a){
  return (new Prims_Nil(a));
  
 });
 (creator['t'])=Prims_Nil;
 return creator;
 
})());
let Example_main=((n) => (((Prims_Cons(Prims_string))(((Prims_op_Hat('fibonacci('))(((Prims_op_Hat((Prims_string_of_int(n))))(((Prims_op_Hat(') => '))((Prims_string_of_int((Example_fibonacci(n))))))))))))((((Prims_Cons(Prims_string))(((Prims_op_Hat('factorial('))(((Prims_op_Hat((Prims_string_of_int(n))))(((Prims_op_Hat(') => '))((Prims_string_of_int((Example_factorial(n))))))))))))((Prims_Nil(Prims_string)))))));
let Example_fibonacci=((n) => ((function (){
 let $1=((Prims_op_LessThanOrEqual(n))(1));
 if (($1===true)){
  return 1;
  
 }if (true){
  let uu___=$1;
  return ((Prims_op_Addition((Example_fibonacci(((Prims_op_Subtraction(n))(1))))))((Example_fibonacci(((Prims_op_Subtraction(n))(2))))));
  
 }throw ('Failed to pattern match '+(($1['constructor'])['name']));
 
})()));
let Example_factorial=((n) => ((function (){
 let $1=(((Prims_op_Equality(Prims_int))(n))(0));
 if (($1===true)){
  return 1;
  
 }if (true){
  let uu___=$1;
  return ((FStar_Mul_op_Star(n))((Example_factorial(((Prims_op_Subtraction(n))(1))))));
  
 }throw ('Failed to pattern match '+(($1['constructor'])['name']));
 
})()));
((console['log'])((Example_main(5))));

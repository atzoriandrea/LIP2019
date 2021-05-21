type ide = Ide of string and param = Value of ide
           | Reference of ide and
parlist = param list and prog = Prog of com and dich = Null
| Dseq of dich * dich
| Var of ide
| Proc of ide * parlist * com
| Fun of ide * parlist * com * exp and com = Nop
| Skip
| Break
| Assign of ide * exp
| Cseq of com * com
| If of exp * com * com
| Repeat of com
| Block of dich * com
| Call of ide * acparlist and exp = Val of ide
| Eint of int
| True
| False
| Empty
| Sum of exp * exp
| Diff of exp * exp
| Times of exp * exp
| And of exp * exp
| Or of exp * exp
| Not of exp
| Eq of exp * exp
| Less of exp * exp
| Cons of exp * exp
| Head of exp
| Tail of exp
| Fst of exp
| Snd of exp
| Epair of exp * exp
| Callf of ide * acparlist and  acpar = Pide of ide
| Pexp of exp and  acparlist = acpar list and  eval = Undefined
| Int of int
| Bool of bool
| List of eval list
| Pair of eval * eval and dval = None
| Dint of int
| Dbool of bool
| Dloc of loc
| Dlist of dval list
| Dpair of dval * dval
| Dfun of parlist * com * exp
| Dproc of parlist * com and  mval = Unassigned
| Mint of int
| Mbool of bool
| Mlist of mval list
| Mpair of mval * mval and loc = L of int and  env = ide -> dval and store = loc -> mval and  flag = Ok | Br;;

let castEnv (envir:env) = envir;;
let castStore (st:store) = st;;
let nextloc = ref (-1);;
let newloc = fun () -> nextloc := !nextloc + 1;
                       L(!nextloc);;

let emptyenv (x:ide) = None;;

let applyenv ((r:env), (x:ide)) = r x;;



let bind ((r:env),(x:ide),(dv:dval))=
  castEnv(
    fun id -> if id=x then dv
              else applyenv (r,id));;

let emptystore (x:loc) =  Unassigned;;

let applystore ((a:store), (b:loc)) = a b;;

let rec update ((s:store),(l:loc),(m:mval)) =
  castStore  (fun id -> if id=l then m
                        else applystore (s,id));;

let dinttoint x = match x with
    Dint a -> a|
    _ -> failwith"NaN_dint";;

let dbooltobool x = match x with
    Dbool a -> a|
    _ -> failwith"NaB";;

let dlisttolist x = match x with
    Dlist a -> a |
    _ -> failwith "NaL";;

let dloctoloc x = match x with
    Dloc a -> a |
    _ -> failwith "NaLoc";;

let rec evaltoint (x:eval) = match x with
    Int o -> o|
    _ -> failwith "NaN_eval";;
let rec evaltobool (x:eval) = match x with
    Bool n -> n|
    _ -> failwith "NaB";;
let rec evaltolist (x:eval) = match x with
    List z -> z|
     _ -> failwith "NaL";;
let rec evaltopair (x:eval) = match x with
    Pair (a,b) -> (a, b)|
    _ -> failwith "NaP";;
    
let rec mvaltoeval (x:mval) = match x with
    Unassigned -> Undefined|
    Mint o -> Int o|
    Mbool o -> Bool o|
    Mlist o -> List (List.fold_right (fun y b-> (mvaltoeval y)::b) o [])|
    Mpair (a,b) -> Pair (mvaltoeval a, mvaltoeval b);;

let rec evaltodval (x:eval) = match x with
    Undefined -> None|
    Int o -> Dint o|
    Bool o -> Dbool o|
    List o -> Dlist (List.fold_right (fun y b-> (evaltodval y)::b) o [])|
    Pair (a,b) -> Dpair(evaltodval a, evaltodval b);;

let rec dvaltomval (x:dval) = match x with
    None -> Unassigned|
    Dint o -> Mint o|
    Dbool o -> Mbool o|
    Dlist o -> Mlist (List.fold_right (fun a b-> (dvaltomval a)::b) o [])|
    Dpair (a,b) -> Mpair (dvaltomval a, dvaltomval b)|
    _ -> failwith "conversione impossibile";;

let pexptoexp (ap:acpar) = match ap with
    Pexp x -> x|
    _ -> failwith "NaExp";;

let rec declare d ((e:env),(s:store))=match d with
   Null -> (e,s)
 | Dseq (d1,d2) -> declare d2 (declare d1 (e,s))
 | Var i -> ((bind (e,i, Dloc (newloc ()))),s)
 | Proc (i,p,c) ->((bind (e,i,Dproc (p,c))), s)
 | Fun (i,p,c,ex) ->((bind (e,i,Dfun (p,c,ex))),s);;

let rec primo x = match x with
    (e1,e2,e3) -> e1
and secondo x = match x with
    (e1,e2,e3) -> e2
and terzo x = match x with
    (e1,e2,e3) -> e3
and exptoeval (x:exp) (e:env) (s:store) = match x with
  Val x->((mvaltoeval (applystore (s,(dloctoloc(applyenv (e,(x))))))),s)
| Eint x-> (Int x,s)
| True->(Bool true,s)
| False->(Bool false,s)
| Empty->(List [],s)
| Sum (a,b)-> let evalA=(exptoeval a e s) in
              let evalB=(exptoeval b e s) in
              (Int ((evaltoint (fst(evalA)))+(evaltoint (fst(evalB)))),snd evalB)
| Diff (a,b)->let evalA=(exptoeval a e s) in
              let evalB=(exptoeval b e s) in
              (Int ((evaltoint (fst(evalA)))-(evaltoint (fst(evalB)))),snd evalB)
| Times (a,b)->let evalA=(exptoeval a e s) in
              let evalB=(exptoeval b e (snd evalA)) in
              (Int ((evaltoint (fst(evalA)))*(evaltoint (fst(evalB)))),snd evalB)
| And (a,b)->let evalA=(exptoeval a e s) in
              let evalB=(exptoeval b e (snd evalA)) in
              (Bool ((evaltobool (fst(evalA)))&&(evaltobool (fst(evalB)))),snd evalB)
| Or (a,b)->let evalA=(exptoeval a e s) in
              let evalB=(exptoeval b e (snd evalA)) in
              (Bool ((evaltobool (fst(evalA)))||(evaltobool (fst(evalB)))),snd evalB)
| Not a->(Bool (not (evaltobool (fst(exptoeval a e s)))), snd(exptoeval a e s))
| Eq (a,b)->let evalA=(exptoeval a e s) in
            let evalB=(exptoeval b e (snd evalA)) in
            let evaleq e1 e2=match (e1,e2) with
                (Undefined,Undefined)->Bool true
               |(Int x,Int y)-> if(x=y) then (Bool true) else (Bool false)
               |(Bool x,Bool y)-> if(x=y) then (Bool true) else (Bool false)
               |(List x,List y)-> if(x=y) then (Bool true) else (Bool false)
               |(Pair (x,y), Pair (x1,y1))->if(x=x1&&y=y1) then (Bool true) else (Bool false)
               |_->failwith "Uguaglianza impossibile" in
              ((evaleq (fst (evalA)) (fst (evalB))),(snd evalB))
| Less (a,b)->let evalA=(exptoeval a e s) in
              let evalB=(exptoeval b e s) in
              (Bool ((evaltoint (fst(evalA)))<(evaltoint (fst(evalB)))),snd evalB)

| Cons (a,b)->let evalA = exptoeval a e s in
              let evalB = exptoeval b e (snd(evalA)) in
              let creaLista elemA elemB = match elemB with
                  List x->List(elemA::x)
                 |_->failwith "Non e' una lista" in
              ( (creaLista (fst(evalA)) (fst(evalB))),snd(evalB))
| Head a ->let evalA = exptoeval a e s in
           let testa l=match l with
               List x-> List.hd x
              |_-> failwith "Non e' lista" in
                     ((testa (fst(evalA))),snd(evalA))
| Tail a->let evalA = exptoeval a e s in
           let coda l=match l with
               List x-> List (List.tl x)
              |_-> failwith "Non e' lista" in
                     ((coda (fst(evalA))),snd(evalA))
| Fst a->(let r = exptoeval a e s in
          match r with
            (Pair (v,b),s) -> (v,s)|
             _ -> failwith "NotACouple"
         )
| Snd a->(let r = exptoeval a e s in
          match r with
            (Pair (v,b),s) -> (b,s)|
             _ -> failwith "NotACouple") 
| Epair (a,b)->let evalA=exptoeval a e s in
               let evalB=exptoeval b e (snd(evalA)) in
              (Pair(fst(evalA),fst(evalB)),snd(evalB))
| Callf (i,l) -> let resu = acpartopar i (applyenv(e,i)) l e s in
                    ( match applyenv(e,i) with
                       Dfun (pl,com,expr) -> let evexp = exec com (fst resu) (snd resu) Ok in
                       exptoeval expr (primo evexp) (secondo evexp) |
                       _ -> failwith "Non è una funzione" )
and exe (p:prog) (e:env) (s:store) =  match p with
    Prog x -> exec x e s Ok
and exec (c:com) (e:env) (s:store) (f:flag) =
  match (c,f) with
    (_,Br) -> failwith "Computazione interrotta - break"|
    (Nop,f) -> (e,s,f)|
    (Skip,f) -> if f = Ok then (e,s,Ok)
	      else failwith "Errore - break"|
    (Break,f) -> if f = Ok then (e,s,Br)
	      else failwith "Errore - break"|
    (Assign (i,exp),f) -> let ev = exptoeval exp e s in
                      let s1 = update((snd ev),dloctoloc(applyenv(e,i)),dvaltomval(evaltodval(fst(ev)))) in
                      exec Nop e s1 Ok|
    (Cseq (c1,c2),f) ->  let e1 = exec c1 e s f in  exec c2 e (secondo e1) (terzo e1) |
    (If (exp,c1,c2),f) -> let r = exptoeval exp e s in if (fst r)= (Bool true) then exec c1 e (snd r) Ok else exec c2 e (snd r) Ok|
    (Repeat com,f) -> let r = exec com e s f in if terzo r = Br then r else exec c e (secondo r) f|
    (Block (d,com),f) -> (let b = declare d (e,s) in exec com (fst b) (snd b) Ok)|
    (Call (i,acpl),f) -> let resu = acpartopar i (applyenv(e,i)) acpl e s in
                     match applyenv(e,i) with
                       Dproc (pl,com) -> exec com (fst resu) (snd resu) Ok |
                       _ -> failwith "Non è una procedura"
and acparconv (pl:parlist) (pa:acparlist) (e:env) (s:store) = match (pl,pa) with
    (ploc::tloc, pact::tact) -> (match (ploc,pact) with
                                  (Value i1,Pide i2) -> let nloc = newloc() in acparconv tloc tact (bind(e,i1,(Dloc nloc))) (update(s,nloc,applystore(s,dloctoloc(applyenv(e,i2)))))|
                                  (Reference r1, Pide i2) -> acparconv tloc tact (bind(e,r1,applyenv(e,i2))) s|
                                  (Value i1, Pexp exp) -> let nloc = newloc() in let ev = exptoeval (pexptoexp pact) e s in acparconv tloc tact (bind(e,i1,(Dloc nloc))) (update ((snd ev),nloc,dvaltomval(evaltodval(fst(ev)))))|
                                _ -> failwith "errore_acparconv")|
    ([],[]) -> (e,s)|
    _ -> failwith "errore!"
and acpartopar (i:ide) (pl:dval) (pa:acparlist) (e:env) (s:store) = match pl with
    Dfun (p,c,ex) ->  if List.length p != List.length pa then
                        failwith "Fun mismatch" else acparconv p pa e s|
    Dproc (p,c) -> if List.length p != List.length pa then
                     failwith "Proc mismatch" else acparconv p pa e s|
    _ -> failwith "Non è una funzione o una procedura";;



                              
                                                                                                                               
                           
    
                                                              
    

let rec semp ((p:prog),(e:env),(s:store)) = let primo x = match x with
    (e1,e2,e3) -> e1 in 
let secondo x = match x with
    (e1,e2,e3) -> e2 in let res = exe p e s in
                        (primo res, secondo res);;
#trace semp


let esegui_programma p = let r = semp (p,emptyenv,emptystore) in evaltodval(mvaltoeval(applystore((snd r),dloctoloc(applyenv ((fst r), Ide"y")))));;


(*Interprete*)
                                          
let p1 = Prog(Block(Var(Ide("y")),Assign(Ide("y"),True)));;
esegui_programma p1;;
let p2 = Prog(Block(Var(Ide("y")),Assign(Ide("y"),Eint(2))));;
esegui_programma p2;;
let p3 = Prog(Block(Dseq(Var(Ide("x")),Dseq(Var(Ide("y")),Null)),
                    Cseq(Assign(Ide("x"),Eint(5)),Assign(Ide("y"),Sum(Eint(1),Val(Ide("x")))))));;
esegui_programma p3;;
let p4 = Prog(Block(Dseq(Var(Ide("x")),Dseq(Var(Ide("y")),Null)),
                  Cseq(Assign(Ide("x"),Eint(5)),
                   Cseq(Assign(Ide("y"),Eint(1)),Repeat(
                                   If(Eq(Val(Ide("x")),Eint(0)),
                                      Break,
                                      Cseq(Assign(Ide("y"),
                                           Times(Val(Ide("y")),Val(Ide("x")))),
                                           Assign(Ide("x"),Diff(Val(Ide("x")),Eint(1))))
                   ))))));;
esegui_programma p4;;
let fun1 = Fun(Ide("fatt"),
               [Value(Ide("x"))],
               Block(Dseq(Var(Ide("y")),Null),
                   Cseq(If(Eq(Val(Ide("x")),Eint(0)),
                        Assign(Ide("y"),Eint(1)),
                        Assign(Ide("y"),Times(Val(Ide("x")),
                                              Callf(Ide("fatt"),[Pexp(Diff(Val(Ide("x")),Eint(1)))])))),
                        Assign(Ide("x"),Val(Ide("y"))))),                      
               Val(Ide("x")));;


let p5 = Prog(Block(
              Dseq(fun1,Dseq(Var(Ide("y")),Null)),
              Cseq(Assign(Ide("y"),Eint(5)),
                   Assign(Ide("y"),Callf(Ide("fatt"),[Pexp(Val(Ide("y")))])))));;

esegui_programma p5;;

let proc1 = Proc(Ide("f"),
                 [Value(Ide("x"));Reference(Ide("z"))],
                  Assign(Ide("z"),Sum(Val(Ide("z")),Val(Ide("x")))));;
let p6 = Prog(Block(
                    Dseq(proc1,Dseq(Var(Ide("y")),Null)),
                    Cseq(Assign(Ide("y"),Eint(5)),Call(Ide("f"),[Pexp(Val(Ide("y")));Pide(Ide("y"))]))
                    )
           );;
esegui_programma p6;;

let p7 = Prog(Block(
                    Dseq(proc1,Dseq(Var(Ide("y")),Null)),
                    Cseq(Assign(Ide("y"),Eint(5)),Cseq(
                                                  Call(Ide("f"),[Pexp(Val(Ide("y")));Pide(Ide("y"))]),
                                                  Call(Ide("f"),[Pexp(Eint(1));Pide(Ide("y"))])
                                                  )
                         )
                    )
         );;

esegui_programma p7;;

let fun2 = Fun(Ide("g"),
               [Value(Ide("x"));Reference(Ide("z"))],
               Assign(Ide("z"),Cons(Val(Ide("x")),Val(Ide("z")))),      
               Val(Ide("z")));;
let p8 = Prog(Block(
                    Dseq(fun2,Dseq(Var(Ide("y")),Null)),
                    Cseq(Assign(Ide("y"),Empty),
                         Assign(Ide("y"),Callf(Ide("g"),[Pexp(Eint(1));Pide(Ide("y"))])))
                    )
           );;


esegui_programma p8;;

let p9 = Prog(Block(
                    Dseq(fun2,Dseq(Var(Ide("y")),Null)),
                    Cseq(Assign(Ide("y"),Empty),
                         Cseq(Assign(Ide("y"),Callf(Ide("g"),[Pexp(Eint(1));Pide(Ide("y"))])),
                              Assign(Ide("y"),Callf(Ide("g"),[Pexp(Eint(1));Pide(Ide("y"))]))
                              )
                         )
                    )
           );;

esegui_programma p9;;

let fun3 = Fun(Ide("insert"),
               [Value(Ide("x"));Value(Ide("z"));Value(Ide("l"))],
               If(Eq(Val(Ide("l")),Eint(0)),
                  Assign(Ide("z"),Cons(Val(Ide("x")),Val(Ide("z")))),
                  If(Less(Val(Ide("x")),Head(Val(Ide("z")))),
                     Assign(Ide("z"),Cons(Head(Val(Ide("z"))),
                                     Callf(Ide("insert"),[Pexp(Val(Ide("x")));Pexp(Tail(Val(Ide("z"))));Pexp(Diff(Val(Ide("l")),Eint(1)))]))),
                     Assign(Ide("z"),Cons(Val(Ide("x")),Val(Ide("z"))))
                     )),
               Val(Ide("z"))
               );;   
let p10 = Prog(Block(
                    Dseq(fun3,Dseq(Var(Ide("y")),Null)),
                    Cseq(Assign(Ide("y"),Cons(Eint(4),Cons(Eint(1),Empty))),
                         Assign(Ide("y"),Callf(Ide("insert"),[Pexp(Eint(3));Pide(Ide("y"));Pexp(Eint(2))]))
                         )
                    )
         );;

esegui_programma p10;;

let fun4 = Fun(Ide("insert"),
               [Value(Ide("x"));Value(Ide("z"));Value(Ide("l"))],
               If(Eq(Val(Ide("l")),Eint(0)),
                 Cseq(Assign(Ide("q"),Sum(Val(Ide("q")),Eint(1))),
                  Assign(Ide("z"),Cons(Val(Ide("x")),Val(Ide("z"))))
                     ),
                 Cseq(Assign(Ide("q"),Sum(Val(Ide("q")),Eint(1))),
                  If(Less(Val(Ide("x")),Head(Val(Ide("z")))),
                     Assign(Ide("z"),Cons(Head(Val(Ide("z"))),
                                     Callf(Ide("insert"),[Pexp(Val(Ide("x")));Pexp(Tail(Val(Ide("z"))));Pexp(Diff(Val(Ide("l")),Eint(1)))]))),
                     Assign(Ide("z"),Cons(Val(Ide("x")),Val(Ide("z"))))
                     ))
                  ),
               Val(Ide("z"))
               );;
let p11 = Prog(Block(
                    Dseq(fun4,Dseq(Var(Ide("y")),Dseq(Var(Ide("q")),Null))),
                    Cseq(Assign(Ide("q"),Eint(0)),
                      Cseq(Assign(Ide("y"),Cons(Eint(4),Cons(Eint(3),Cons(Eint(1),Empty)))),
                           Assign(Ide("y"),Callf(Ide("insert"),[Pexp(Eint(2));Pide(Ide("y"));Pexp(Eint(3))]))
                         )
                         )
                    )
            );;

esegui_programma p11;;

let p12 = Prog(Block(
                    Dseq(Var(Ide("y")),Null),
                    Cseq(Assign(Ide("y"),Eint(0)),
                         Repeat(If(True,Skip,Break))
                         )
                    )
            );; (*Non termina*)
esegui_programma p12;;

let p13 = Prog(Block(
                    Dseq(Var(Ide("y")),Null),
                    Cseq(Assign(Ide("y"),Eint(0)),
                         Break
                         )
                    )
            );;
esegui_programma p13;;

let p14 = Prog(Block(
                    Dseq(Var(Ide("y")),Null),
                    Cseq(Assign(Ide("y"),Eint(0)),
                         Cseq(Skip,Break)
                         )
                    )
            );;

esegui_programma p14;;
let p15 = Prog(Block(
                    Dseq(fun3,Dseq(Var(Ide("y")),Dseq(Var(Ide("q")),Null))),
                    Cseq(Assign(Ide("q"),Eint(0)),
                      Cseq(Assign(Ide("y"),Cons(Eint(4),Cons(Eint(3),Empty))),
                         Cseq(
                           Assign(Ide("y"),Callf(Ide("insert"),[Pexp(Eint(1));Pide(Ide("y"));Pexp(Eint(2))])),
                           Assign(Ide("y"),And(True,Val(Ide("y"))))
                             )
                          )
                        )
                      )
               );;         
(* deve fallire a causa del And tra un booleano e una lista *)
esegui_programma p15;;

let fun5 =  Fun(Ide("crea"),
               [Value(Ide("x"));Value(Ide("z"))],
               If(Eq(Val(Ide("x")),Eint(0)),
                  Assign(Ide("z"),Empty),
                  Assign(Ide("z"),Cons(Val(Ide("x")),Callf(Ide("crea"),[Pexp(Diff(Val(Ide("x")),Eint(1)));Pexp(Val(Ide("z")))])))
                  ),
               Val(Ide("z"))
               );;
let p16 = Prog(Block(
                    Dseq(fun5,Dseq(Var(Ide("y")),Dseq(Var(Ide("q")),Null))),
                    Cseq(Assign(Ide("q"),Eint(10)),
                    Assign(Ide("y"),Callf(Ide("crea"),[Pexp(Val(Ide("q")));Pexp(Empty)]))
                         )
                    )
         );;
(* Dlist [Dint 10; Dint 9; Dint 8; Dint 7; Dint 6; Dint 5; Dint 4; Dint 3; Dint 2;
  Dint 1] *)
esegui_programma p16;;


let fun6 = Fun(Ide("coppia"),
               [Value(Ide("x"));Reference(Ide("z"))],
                Block(Dseq(Var(Ide("y")),Dseq(Var(Ide("w")),Null)),
                      Cseq(Assign(Ide("w"),Snd(Val(Ide("x")))),
                           Cseq(Assign(Ide("y"),Fst(Val(Ide("x")))),
                           Assign(Ide("z"),Epair(Callf(Ide("crea"),[Pexp(Val(Ide("w")));Pexp(Val(Ide("y")))]),Val(Ide("w"))))))),
               Val(Ide("z")));;
let p17 = Prog(Block(
                    Dseq(fun5,Dseq(fun6,Dseq(Var(Ide("y")),Null))),
                    Cseq(Skip,
                    Cseq(Assign(Ide("y"),Epair(Empty,Eint(5))),
                    Assign(Ide("y"),Callf(Ide("coppia"),[Pexp(Val(Ide("y")));Pide(Ide("y"))]))
                         )
                    ))
         );;               
(*  Dpair (Dlist [Dint 5; Dint 4; Dint 3; Dint 2; Dint 1], Dint 5) *)
esegui_programma p17;;


let p18 = Prog(Block(
                    Dseq(Proc(Ide("f"),[Reference(Ide("x"))],Assign(Ide("x"),Eint(120))),
                         Dseq(Var(Ide("y")),Null)),
                    Call(Ide("f"),[Pide(Ide("y"))])));; 
(* Dint 120 *)
esegui_programma p18;;

let p19 = Prog(Block(
                    Dseq(Fun(Ide("f"),[Reference(Ide("x"))],Assign(Ide("x"),Eint(120)),Eint(1)),
                         Dseq(Var(Ide("y")),Dseq(Var(Ide("z")),Null))),
                    Assign(Ide("z"),Callf(Ide("f"),[Pide(Ide("y"))]))));;

esegui_programma p19;;

let p20 = Prog(Block(
                    Dseq(Proc(Ide("f"),[Reference(Ide("x"))],Assign(Ide("x"),Eint(120))),
                      Dseq(Proc(Ide("g"),[Reference(Ide("h"));Reference(Ide("z"))],Call(Ide("z"),[Pide(Ide("h"))])),
                        Dseq(Var(Ide("y")),Null))),
                    Cseq(Skip,Cseq(Assign(Ide("y"),Eint(14)),Cseq(Call(Ide("g"),[Pide(Ide("y"));Pide(Ide("f"))]),Skip)))));;                                      
(* Dint 120 *)
esegui_programma p20;;






let primo x = match x with
    (e1,e2,e3) -> e1;;
let secondo x = match x with
    (e1,e2,e3) -> e2;;
                    

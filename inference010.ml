(*Nella seconda parte dovete scrivere una funzione in Ocaml che realizza la type inference che si chiama typeinf e che ha tipo exp -> etype  *)

(*identificatore  delle variabili*)
type ide = Ide of string;;
(*SINTASSI LINGUAGGIO*)
type param = Value of ide
           | Reference of ide ;;
type parlist = param list ;;
type prog = Prog of com and dich = Null
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

(*Per la seconda parte del progetto, il tipo in Ocaml per i tipi del linguaggio `e il seguente:*)
type etype =
    TBool
  | TInt
  | TVar of string
  | TPair of etype * etype
  | TList of etype list

(*e per generare ogni volta una nuova variabile dovete usare il seguente codice:*)
let nextsym = ref (-1);;
let newvar = fun () -> nextsym := !nextsym + 1;
TVar ("?T" ^ string_of_int (!nextsym));;

(*Queste righe di codice Ocaml hanno una parte imperativa per generare un nuovo numero, dovete usarla.
L’ambiente per i tipi (type) ha come come tipo (ide * etype) list ed ha una funzione per creare un ambiente per i tipi che si chiama newtypenv, una per ottenere il tipo associato ad un ide che si chiama applytypenv ed un modo per aggiungere o modificare un legame che `e bindtyp che riceve un ambiente per tipi, un elemento di tipo ide ed un valore di tipo e restituisce l’ambiente per tipi aggiornato.
Il file contenente la soluzione deve contenere le adeguate definizioni di funzione in modo da generare i seguenti valori di tipo in Ocaml. Le funzioni ausiliarie possono avere qualsiasi nome.
val nextsym : int ref {contents = -1}
val newvar : unit -> etype = <fun>
val newtypenv : (ide * etype) list
val applytypenv : (ide * etype) list -> ide -> etype = <fun>
val bindtyp : (ide * etype) list -> ide -> etype -> (ide * etype) list = <fun>
  val typeinf : exp -> etype  = <fun>*)


(*FUNZIONI GESTIONE AMBIENTE *)
(*creazione ambiente per i tipi*)
let newtypenv=
  let initNewtypenv l= match l with
    (Ide "",TVar "")::tl->tl
   |tl->tl in initNewtypenv [(Ide "",TVar "")];;

(*assocciazione tipo ad identificatore*)
(*let rec bindtyp (a:(ide*etype) list) (i:ide) (e:etype) =match a with
    []->[(i,e)]
  |(i1,TVar s1)::a1->(i1,TVar s1)::bindtyp a1 i e
  |(i1,e1)::a1->if i=i1 then (i1,e)::a1 else (i1,e1)::bindtyp a1 i e;;*)

let bindtyp env (i:ide) (et:etype) = match env with
    [] -> (i, et) :: []
  | (l, e)::tl -> (i, et) :: (l, e) :: tl;;
exception TypeExcept;;

(*restituzione tipo associato all'identificatore*)
let rec applytypenv (a:(ide*etype) list) (i:ide) = match a with
   (i1,e1)::a1-> if i = i1 then e1 else applytypenv a1 i|
   []-> let newv = newvar() in let env = bindtyp a i newv in applytypenv env i;;


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
(*Conversioni*)
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
    List (hd::tl) -> hd :: tl|
    List [] -> []|
     _ -> failwith "NaL";;
let rec evaltopair (x:eval) = match x with
    Pair (a,b) -> (a, b)|
    _ -> failwith "NaP";;
    
let rec mvaltoeval (x:mval) = match x with
    Unassigned -> Undefined|
    Mint o -> Int o|
    Mbool o -> Bool o|
    Mlist (hd::tl) -> List (mvaltoeval hd :: [mvaltoeval (Mlist tl)])|
    Mlist [] -> List []|
    Mpair (a,b) -> Pair (mvaltoeval a, mvaltoeval b);;

let rec evaltodval (x:eval) = match x with
    Undefined -> None|
    Int o -> Dint o|
    Bool o -> Dbool o|
    List (hd::tl) -> Dlist (evaltodval hd :: [evaltodval (List tl)])|
    List [] -> Dlist []|
    Pair (a,b) -> Dpair(evaltodval a, evaltodval b);;

let rec dvaltomval (x:dval) = match x with
    None -> Unassigned|
    Dint o -> Mint o|
    Dbool o -> Mbool o|
    Dlist (hd::tl) -> Mlist (dvaltomval hd :: [dvaltomval (Dlist tl)])|
    Dlist [] -> Mlist []|
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

(*INFERENZA DEI TIPI*)
(*generazione vincoli per l'inferenza*)
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
              let creaLista elemA elemB=match elemB with
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
| Fst a->(*expIsEpair a true s*) (Int 5,s)
| Snd a->(*expIsEpair a false s*) (Int 5,s)
| Epair (a,b)->let evalA=exptoeval a e s in
               let evalB=exptoeval b e (snd(evalA)) in
              (Pair(fst(evalA),fst(evalB)),snd(evalB))
| Callf (i,l) -> let resu = acpartopar i (applyenv(e,i)) l e s in
                    ( match applyenv(e,i) with
                       Dfun (pl,com,expr) -> let evexp = exe (Prog com) (fst resu) (snd resu) in
                       exptoeval expr (primo evexp) (secondo evexp) |
                       _ -> failwith "Non è una funzione" )
and typei (expr:exp) (envir:(ide * etype) list) (e:env) (s:store) =match expr with
      Val id->(applytypenv envir id),[]
    | Eint n-> TInt,[]
    | True | False->TBool,[]
    | Empty->TList(newvar()::[]),[]
    | Sum (n1,n2) |Diff (n1,n2)|Times (n1,n2)->
			 let typ1,v1= typei n1 envir e s  in
			 let typ2,v2= typei n2 envir e s in
			 (TInt,[(typ1,TInt)]@[(typ2,TInt)]@v1@v2)			 
    | And (b1,b2)| Or (b1,b2)->
	   let typ1,v1= typei b1 envir e s in
	   let typ2,v2= typei b2 envir e s in
	   (TBool,[(typ1,TBool)]@[(typ2,TBool)]@v1@v2)   
    | Not b->
       let typ,v= typei b envir e s in
         (TBool,[(typ,TBool)]@v) 
    | Less (n1,n2)->
        let typ1,v1= typei n1 envir e s in
	let typ2,v2= typei n2 envir e s in
       (TBool,[(typ1,TInt)]@[(typ2,TInt)]@v1@v2)
    | Eq (a1,a2)->
       	let tVar=newvar() in
        let typ1,v1= typei a1 envir e s in
	let typ2,v2= typei a2 envir e s in
       (TBool,v1@v2@[(typ1,tVar)]@[(typ2,tVar)])
    | Head (t)->
       let tVar=newvar() in
       let typ,v= typei t envir e s in
       (tVar,v@[(typ,TList(tVar::[]))])    
    | Tail (t)->
       let tVar=newvar() in
       let typ,v= typei t envir e s in
       (TList(tVar::[]),v@[(typ,TList(tVar::[]))])
     | Cons (h,t)->
	let tVar=newvar() in
	let typ1,v1= typei h envir e s in
	let typ2,v2= typei t envir e s in
	(TList(tVar::[]),v1@v2@[(typ1,tVar)]@[(typ2,TList(tVar::[]))])
     | Fst (x)->
	let tVarS=newvar() in
	let tVarD=newvar() in
	let typ,v= typei x envir e s in
	(tVarS,v@[(typ,TPair(tVarS,tVarD))])
     | Snd (x)->
	let tVarS=newvar() in
	let tVarD=newvar() in
	let typ,v= typei x envir e s in
	(tVarD,v@[(typ,TPair(tVarS,tVarD))])
     | Epair (x1,x2)->
	let tVarS=newvar() in
	let tVarD=newvar() in
	let typ1,v1= typei x1 envir e s in
	let typ2,v2= typei x2 envir e s in
	(TPair(tVarS,tVarD),v1@v2@[(typ1,tVarS)]@[(typ2,tVarD)])
     | Callf (ide,acpar) -> let resu = acpartopar ide (applyenv(e,ide)) acpar e s in
                    ( match applyenv(e,ide) with
                       Dfun (pl,com,expr) -> let evexp = exe (Prog com) (fst resu) (snd resu) in
                       typei expr envir (primo evexp) (secondo evexp))
and exe (p:prog) (e:env) (s:store) = let rec exec (c:com) (e:env) (s:store) (f:flag) =
  match c with
    Nop -> (e,s,f)|
    Skip -> exec Nop e s Ok|
    Break -> exec Nop e s Br|
    Assign (i,exp) -> let ev = exptoeval exp e s in
                      let s1 = update((snd ev),dloctoloc(applyenv(e,i)),dvaltomval(evaltodval(fst(ev)))) in
                      exec Nop e s1 Ok|
    Cseq (c1,c2) ->  let e1 = exec c1 e s f in  exec c2 e (secondo e1) (terzo e1) |
    If (exp,c1,c2) -> if (fst (exptoeval exp e s))= (Bool true) then exec c1 e s Ok else exec c2 e s Ok|
    Repeat com -> exec com e s f|
    Block (d,com) -> (let b = declare d (e,s) in exec com (fst b) (snd b) Ok)|
    Call (i,acpl) -> let resu = acpartopar i (applyenv(e,i)) acpl e s in
                     match applyenv(e,i) with
                       Dproc (pl,com) -> exec com (fst resu) (snd resu) Ok |
                       _ -> failwith "Non è una procedura"
                     in
                   match p with
                     Prog x -> exec x e s Ok
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
    _ -> failwith "Non è una funzione o una procedura!";;                                       
          
                      
                                  
(*cambia valore associato a una variabile di tipo*)
let rec changetypV (vinc:etype) (tVar:etype) (t:etype)=match vinc with
    TPair(tVar1,tVar2)->
         TPair((changetypV tVar1 (tVar) t) ,(changetypV tVar2 (tVar) t))
  | TList(tVar1::[])->
         TList((changetypV tVar1 (tVar) t)::[])
  | tVar1->
     if tVar1=tVar then t
     else tVar1;;

(*cambia valore associato a una variabile di tipo nei vincoli*)
let rec changeofList (tVar:etype) (t:etype) (l:(etype*etype) list)=match l with
     []->[]
    |(sx,dx)::tl->
       ((changetypV sx tVar t),(changetypV dx tVar t)) ::changeofList tVar t tl;;

(*algoritmo di sostituzione*)      
let rec s (ident:etype) ((v:etype*etype),(lv:(etype*etype) list))=match v with
    |(a,b) when a=b->(ident,lv)
    |(TVar s1,a)|(a,TVar s1)->
      ((changetypV ident (TVar s1) a),(changeofList (TVar s1) a lv))
    |(TPair(a1,a2),TPair(b1,b2))->
      let newIdent,newvinc=s ident ((a1,b1),v::lv) in
      let newIdent1,newvinc1=s newIdent ((a2,b2),newvinc) in
      (newIdent1,newvinc1) 
    |(TList(a::[]),TList(b::[]))->
      let newIdent,newvinc=s ident ((a,b),v::lv) in
      (newIdent,newvinc)
  |(a,b)->raise TypeExcept;;

(*applicazione algoritmo di sostituzione*) 
let rec sFun (ident,vincoli)= match vincoli with
     []->ident,vincoli
    |(hd::t)->let newident,newvinc=s ident (hd,t) in
       sFun(newident, newvinc);;
(*type inference*)

let prepara (e,d) = match e with
      Callf(z,p) -> (let (r,s) = declare d ((emptyenv),(emptystore)) in
                     match applyenv (r,z) with
                       Dfun(l,c,e1) -> e1|
                       _ -> failwith("Callf is invoked but the identifies is not a function"))

   |_ -> e;;
let typeinf expr=  fst(sFun(typei expr newtypenv emptyenv emptystore));;
                                     


(*Prove*)
let e1 = True;; (* (TBool) *)
typeinf e1;;
let e2 = Eint 1;; (* (TInt) *)
typeinf e2;;
let e3 = Less(Eint 1, Eint 1);; (* (TBool) *)
typeinf e3;;
let e4 = Sum(Eint 1,Eint 2);; (* (TInt) *)
typeinf e4;;
let e5 = Epair(Eint 1,False);; (* (TPair(TInt,TBool)) *)
typeinf e5;;
let e6 = Fst(Epair(Eint 1,False));; (* (TInt) *)
typeinf e6;;
let e7 = Snd(Epair(Eint 1,False));;  (* (TBool) *)
typeinf e7;;
let e8 = Eq(Fst(Epair(Eint 1,Eint 2)),Snd(Epair(Eint 1,Eint 2)));;  (* (TBool) *)
typeinf e8;;
let e9 = Less(Fst(Epair(Eint 1,Eint 2)),Snd(Epair(Eint 1,Eint 2)));; (* (TBool) *)
typeinf e9;;
let e10 = Empty;; (* (TList [TVar "?T0"]) *)
typeinf e10;;
let e11 = Cons(Empty,Empty);;  (* (TList [TList [TVar "?T0"]]) *)
typeinf e11;;
let e12 = Cons(Eint 1,Empty);;  (* (TList [TInt]) *)
typeinf e12;;
let e13 = Head(Cons(Eint 1,Empty));; (* (TInt) *)
typeinf e13;;
let e14 = Tail(Cons(Eint 1,Empty));; (* (TList [TInt]) *)
typeinf e14;;
let e15 = Cons(Cons(True,Empty),Empty);; (* (TList [TList [TBool]]) *)
typeinf e15;;
let e16 = Head(Cons(Empty,Empty));; (* (TList [TVar "?T0"]) *)
typeinf e16;;
let e17 = Val(Ide("x"));; (* (TVar "?T0") *)
typeinf e17;;
let e18 = Sum( Val(Ide("x")), Val(Ide("y")));; (* (TInt) *)
typeinf e18;;
(* nell'espressione qui di sequito Ide("fatt") corrisponde alla dichiarazione*)
let c = Fun(Ide("fatt"),
       [Value(Ide("x"))],
        Block(Dseq(Var(Ide("y")),Null),
             If(Eq(Val(Ide("x")),Eint(0)),
                Assign(Ide("y"),Eint(1)),
                Assign(Ide("y"),Eint 2))),
        Val(Ide("y")));; 
let e19 = Callf (Ide"fatt", [Pexp ( Eint 0)]);;
(* (TVar "?T0") *)
let p = prepara (e19,c);;
typeinf p;;


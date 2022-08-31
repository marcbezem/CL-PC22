%swipl has claimed keyword 'false' and changed numbervars/4; we now use 'fAlse'
:-op(1200, xfx, axiom). :-op(1199, xfx, =>). :-dynamic dom/1,fAlse/0,goal/0,coqlog/0.

valid0(_, _ , Stack,Env,Ni,No) :- 
                 fAlse,!,log(Ni,No,Env,fAlse_ind(goal),fAlse,goal),
                 nl,w1('falid, stack: '),report(Stack).
valid0(Grd,Parnum,Stack,Env,Ni,No):- 
       (A axiom Rule:(Conj => Disj)) %NB order of next 2 lines  
       ,(var(A)->Gnew=Grd;enabled(A,Grd),next(A,Grd,Gnew))
       ,invalid(Conj => Disj),log(Ni,N,Env,Rule,Conj,Disj)
       ,w1('By '),coq_ter(Rule),w1(' using '),coq_con(Conj),w1(' we have:'),nl
       ->
       (Disj=goal ->w1('goal'),nl,nl,w1('valid, stack: '),report(Stack),N=No   
         ;Disj=(E;D)->% IF disjunction THEN push and branch ELSIF ...  
                      report(Disj),nl,w1('stack pushed, stack: '),report([Disj|Stack]),
                      /*branch*/ valid2(Gnew,Parnum,[D|Stack],E,Env,N,M),
                                 log(M,No,Env,or_elim(Ni),Disj,goal)
         ;/*ELSIF*/ground(Disj)->valid1(Gnew,Parnum,Stack,Disj,Env,N,No)
         ;/*existential formula*/valid1(Gnew,Parnum,Stack,Disj,[Disj|Env],N,M),
                               log(M,No,Env,ex_elim(Ni),Disj,goal))
       %ELSE part to main implication
       ;number(Grd),w1(Grd),next(_,Grd,Gnew),!,valid0(Gnew,Parnum,Stack,Env,Ni,No).
                      
valid1(G,Parnum,Stack,E,Env,Ni,No) :- 
             numbervars(E,Parnum,Parnew,[functor_name(par)]), % instantiate
             add_con(E,L),del_dom(E,C),coq_con(C),nl,        % add facts
             valid0(G,Parnew,Stack,Env,Ni,No), 
             sub_con(L).                                     % subtract

valid2(G,P,[T|S],E,Env,Ni,No) :- 
                       nl,w1('stack top tailed: '),
                       valid1(G,P,[T|S],E,[E|Env],Ni,N),
                       (T=(E1;D) -> % IF disjunction THEN branch
                                    valid2(G,P,[D|S],E1,Env,N,No) ;
                                    % ELSE pop stack and continue
                                    nl,w1('stack popped: '),
                                    valid1(G,P,S,T,[T|Env],N,No)).

add_con(C,L):-C=(A,C1)->assertz(A,R),L=[R|Ln],add_con(C1,Ln)
                       ;assertz(C,R),L=[R].
sub_con(L)  :-L=[R|L1]->erase(R),sub_con(L1) ; L=[].

% Coq back-end 

coq_dis(D) :- D=(E;D1)->coq_exi(E),w1(' \\/ '),coq_dis(D1)  ;coq_exi(D).
coq_exi(E) :- E=(dom(Var),E1)->
     rndbra((w3('exists ',Var,', '),coq_exi(E1)))     ;coq_con(E).
coq_con(C) :- C=(F,C1)->coq_ter(F),w1(' /\\ '),coq_con(C1)    ;coq_ter(C).
coq_ter(F) :- coqlog->(compound(F)->once((par_var(F);F=..L,coq_lis(L)));w1(F))
              ;F=..[H|T],w1(H),(T=[]->true;rndbra(arg_lis(T))).
coq_lis([H|T]):- coq_ter(H),once((T=[];w1(' '),coq_lis(T))).
arg_lis([H|T]) :- once((par_var(H);w1(H))),once((T=[];w1(','),arg_lis(T))).

coq_signature:- w1('Let fAlse := False.'),nl,
w1('Let fAlse_ind := False_ind.'),nl,nl,w1('Variable dom : Set.'),nl,
setof(ar(U,N),A^X^Y^Z^F^((A axiom X:(Y=>Z)),in_dis(F,Z),functor(F,U,N)),L0),
(member(ar(goal,0),L0)->L1=L0;L1=[ar(goal,0)|L0]),
coq_sig(L1),(bagof(X,dom(X),L)->w1('Variables '),coq_par(L),w1('.'),nl,nl;true).

coq_sig(L):- L=[ar(U,N)|T]->once((U=',';U=';';U=dom;U=fAlse
            ;w3('Variable ',U,' : '),coq_typ(N),nl)),coq_sig(T)   ;L=[]. 
coq_typ(N):-N=0->w1('Prop.');w1('dom -> '),M is N-1,coq_typ(M).

coq_theory:- forall(((_ axiom X:(Y=>Z)),numbervars(X:(Y=>Z),0,_)),
 (X=..[H|T],w3('Hypothesis ',H,' : '),once((T=[];w1('forall '),coq_par(T),w1(',
  '))),
  del_dom(Y,Y1), once((Y1=true;coq_con(Y1),w1(' -> '))),coq_dis(Z),w1('.'),nl,nl)).
coq_par(L):- L=[V]->w2(V,' : dom');L=[V,H|T],w2(V,' '),coq_par([H|T]).

coq_out :- (name(F),w3('Section ',F,.),nl,nl,coq_signature,coq_theory,
               w3('Theorem ',F,' : goal.'),nl,
               w1('Proof.'),nl,
               w1('exact'),
               once(lemma(N,[],_:_)),lem_prf(0,N),w1('.'),nl,
               w1('Qed.'),nl,nl,
               w3('End ',F,.),nl)->true;w1('noproof').

lem_prf(O,N):- nl,wl(O),w3('(*',N,'*)'),
               rndbra((lemma(N,_,P:_),coq_prf(O,P))),
               /*nl,wl(O),*/w3('(*',N,'*)').

wl(0). wl(s(O)):-w1(' '),wl(O).

coq_prf(O,ap(Ax,Cond)) :- 
   Ax=or_elim(N) -> log(N,_,_,_,_),coq_ors(O,Cond),lem_prf(O,N)
;  Ax=ex_elim(N) -> log(N,_,_,_,_),nl,wl(O),coq_rel(O,Cond),lem_prf(O,N)
;  /*axiom*/ Cond=[]->coq_ter(Ax);coq_ter(Ax),coq_args(s(O),Cond).

coq_ors(O,[E|D]):-D=[]->nl,wl(s(O)),coq_rel(s(O),E)
;  nl,wl(O),rndbra((w1('or_ind '),nl,wl(s(O)),coq_rel(s(O),E),coq_ors(O,D))).

coq_rel(O,N):-log(N,[H|T],_,_,_),(H=(dom(X),C)->rndbra((w1('ex_ind '),
   rndbra((w1('P:='),lambda(abstract(dom(X))),coq_con(C))),%w1(' goal '),
   nl,wl(s(O)),rndbra((lambda(abstract(dom(X))),coq_ands(s(O),N,C,T)))))
                                ;coq_ands(O,N,H,T)).

coq_ands(O,N,C,T):-rndbra((C=(F1,C1)->
   w1('and_ind '),rndbra((lambda(abstract(F1)),coq_ands(O,N,C1,T)))
;  lambda(abstract(C)),lem_prf(s(O),N))).

coq_args(O,L):- L=[H1,H2|T]->w1(' '),rndbra((w1('conj '),
          coq_1arg(O,H1),coq_args(O,[H2|T])));L=[H]->w1(' '),coq_1arg(O,H);L=[].
coq_1arg(O,X):- number(X),log(X,_,_,_,_) -> lem_prf(O,X)
            ; X=M:N -> rndbra((w3(proj,M,' '),coq_1arg(O,N)))
            ;/*the case where X is in the environment*/ inh_name(X).

% proof reconstruction from log
 
prf_out :- forall(log(N,Env,Rule,Prem,Conc), 
   ((Rule=or_elim(_) -> prf_dis(N,Env,Prem,L)
    ;Rule=ex_elim(_) -> M is N-1,L=M
    ;/*axiom applied*/ del_dom(Prem,C),prf_con(Env,C,L)),
    X=lemma(N,Env,ap(Rule,L):Conc),asserta(X),numbervars(X,0,_),w2(X,.),nl
   )             ), prf_prf.

prf_con(Env,(F,C),[N|L]) :- !,prf_fact(Env,F,N),prf_con(Env,C,L).
prf_con(Env, F   ,   L ) :-  F=true -> L=[]; prf_fact(Env,F,N),L=[N].

prf_dis(N,Env,(E;D),[M|L]):-!,log(M,[E|Env],_,_,goal),prf_dis(N,Env,D,L).
prf_dis(N, _ ,  _  , [M] ):-M is N-1.

prf_fact(Env,F,N) :- once((in_env(F,Env),N=F /*F in Env or in log*/
; log(M,E,_,_,C),ground(C),append(_,E,Env),in_con(F,C,M,N))).

prf_prf :- once(lemma(N,_,_)),prf_prf([N],[]). 
prf_prf( [],Prf) :- sort(Prf,P),write(P),nl,assert(proof(P)).                   
prf_prf([H|T],P) :- (lemma(H,_,ap(or_elim(N),L):_) -> append(L,[N|T],Tn)
                    ;lemma(H,_,ap(ex_elim(N),L):_) -> Tn=[L,N|T]
                    ;lemma(H,_,ap(_,L):_),n(L,[],Ln),append(Ln,T,Tn)),
                    prf_prf(Tn,[H|P]).
prf_no :- w1('not used:'),nl,proof(P),forall(_ axiom A:_,
         (member(N,P),lemma(N,_,ap(A,_):_) ;functor(A,F,_),write(F),nl)),
         once(lemma(N,_,_)),w2(N,' is your lucky number'),nl.


%%%%%%%avoid reading this monolithic block with silly auxiliaries%%%%%%%
invalid(C => D):- C,\+ D. 
compile(_).%compile(X):-compile_predicates([X]).
w1(X):-write_term(X,[numbervars(true)]). 
w2(X,Y):-w1(X),w1(Y). w3(X,Y,Z):-w1(X),w2(Y,Z).
log(Ni,No,E,P,C,D):-No is Ni+1,assertz(log(Ni,E,P,C,D)).
in_env(F,[H|T]):-once(in_con(F,H,_,_);in_env(F,T)).% F occurs in environment?
in_dis(F,D):-in_con(F,D,_,_);D=(C;D1),(in_con(F,C,_,_);in_dis(F,D1)).
in_con(F,C,N,M):-C=F,M=N;C=(A,C1),(A=F,M=1:N;in_con(F,C1,2:N,M)). n([],L,L). 
n([H|T],L,Ln):-H=_:N->n([N|T],L,Ln);number(H)->n(T,[H|L],Ln);n(T,L,Ln).
lem_name(N):- ground(N),name(X),w2(X,N).          
par_var(X):- X=par(N),w2('w_',N);X='$VAR'(_),w1(X).      
inh_name(X):- ground(X),w1('V'),factname(X).%CHALLENGING naming scheme!
factname(X):- once((par_var(X);ground(X),X=..[H|T],w1(H),%writing
                                checklist(factname,T))). %flattened facts
par_inh(F):- F=dom(par(N))->w2('w_',N);F=true->true;inh_name(F).
abstract(F):- par_inh(F),w1(' ').
product(F):- F=dom(par(N))->w3('forall w_',N,', ');coq_ter(F),w1(' -> ').
rndbra(X):-w1('('),call(X),w1(')').%enclosing the writes of X by (,)
quotes(X):-w1('"'),call(X),w1('"').%enclosing the writes of X by ","
lambda(X):-w1('fun '),call(X),w1(' => ').
prfqed(X):-w1('Proof.'),nl,w1('exact '),X,w1('.'),nl,w1('Qed.').% Proof-Qed enclosing 
del_dom(C,X):- C=(dom(_),Y)->del_dom(Y,X);C=dom(_)->X=true;C=X.
ext(F,E,FE):- atom_concat(F,'.',F1),atom_concat(F1,E,FE).
io(Dest,Mode,Name,DO):-open(Dest,Mode,_,[alias(Name)]),
       (Mode=write->set_output(Name);set_input(Name)),DO,close(Name).
test(File):- ext(File,in,Fi),cleanup,[Fi],valid0([],0,[],[],1,_),nl.
out(Fi):-ext(Fi,out,Fo),io(Fo,write,out,test(Fi)).
tptp(File):-ext(File,in,Fi),ext(File,p,Fo),cleanup,[Fi],io(Fo,write,tptp,tptp_out).
prf(Fi):-ext(Fi,prf,Fo),io(Fo,write,prf,prf_out),prf_no.
coq(Fi):-ext(Fi,v,Fv),assert(coqlog),io(Fv,write,coq,coq_out),retract(coqlog).
run(File):-out(File),prf(File),coq(File).
cleanup :- abolish(log/5),abolish(lemma/3),
           forall(dynamic_not_built_in(X),retractall(X)).
dynamic_not_built_in(X) :- predicate_property(X,dynamic),\+predicate_property(X,built_in).
 report(S)     :- numbervars(S,0,_),freport(S);nl. %freport reports and 
freport([D|S]) :- !,coq_dis(D),w1(' :: '),freport(S).
freport(X)     :- (X=[]->w1(nil);coq_dis(X)),fail. %fails to undo bindings

%%%%%%%%%%%%%%%experimental


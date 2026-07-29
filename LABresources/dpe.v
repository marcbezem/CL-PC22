Section dpe.

Let fAlse := False.
Let fAlse_ind := False_ind.

Variable dom : Set.
Variable e : dom -> dom -> Prop.
Variable goal : Prop.
Variable r : dom -> dom -> Prop.
Variable re : dom -> dom -> Prop.
Variables a b c : dom.

Hypothesis assump : re a b /\ re a c.

Hypothesis goal_ax : forall A : dom,
  re b A /\ re c A -> goal.

Hypothesis ref_e : forall A : dom,
  e A A.

Hypothesis sym_e : forall A B : dom,
  e A B -> e B A.

Hypothesis congl : forall A B C : dom,
  e A B /\ re B C -> re A C.

Hypothesis e_in_re : forall A B : dom,
  e A B -> re A B.

Hypothesis r_in_re : forall A B : dom,
  r A B -> re A B.

Hypothesis e_or_r : forall A B : dom,
  re A B -> e A B \/ r A B.

Hypothesis dp : forall A B C : dom,
  r A B /\ r A C -> (exists D, r B D /\ r C D).

Theorem dpe : goal.
Proof.
exact
(*29*)(
(or_ind 
 (fun Veab  => 
  (*11*)(goal_ax c (conj 
   (*10*)(congl b a c (conj 
    (*9*)(sym_e a b Veab)(*9*) (proj2 
    (*1*)(assump)(*1*))))(*10*) 
   (*7*)(e_in_re c c 
    (*4*)(ref_e c)(*4*))(*7*)))(*11*))
 (fun Vrab  => 
  (*28*)(
  (or_ind 
   (fun Veac  => 
    (*15*)(goal_ax b (conj 
     (*6*)(e_in_re b b 
      (*3*)(ref_e b)(*3*))(*6*) 
     (*14*)(congl c a b (conj 
      (*13*)(sym_e a c Veac)(*13*) (proj1 
      (*1*)(assump)(*1*))))(*14*)))(*15*))
   (fun Vrac  => 
    (*27*)(
    (ex_ind (P:=fun w_0  => r b w_0 /\ r b w_0)
     (fun w_0  => (and_ind (fun Vrbw_0  => (fun Vrbw_0  => 
      (*26*)(
      (ex_ind (P:=fun w_1  => r b w_1 /\ r c w_1)
       (fun w_1  => (and_ind (fun Vrbw_1  => (fun Vrcw_1  => 
        (*25*)(goal_ax w_1 (conj 
         (*23*)(r_in_re b w_1 Vrbw_1)(*23*) 
         (*24*)(r_in_re c w_1 Vrcw_1)(*24*)))(*25*))))))
      (*20*)(dp a b c (conj Vrab Vrac))(*20*))(*26*))))))
    (*16*)(dp a b b (conj Vrab Vrab))(*16*))(*27*)))
  (*12*)(e_or_r a c (proj2 
   (*1*)(assump)(*1*)))(*12*))(*28*)))
(*8*)(e_or_r a b (proj1 
 (*1*)(assump)(*1*)))(*8*))(*29*).
Qed.

End dpe.

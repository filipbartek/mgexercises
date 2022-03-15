Definition True : prop := forall p:prop, p -> p.
Definition False : prop := forall p:prop, p.

Definition not : prop -> prop := fun A:prop => A -> False.

(* Unicode ~ "00ac" *)
Prefix ~ 700 := not.

Definition and : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> B -> p) -> p.

(* Unicode /\ "2227" *)
Infix /\ 780 left := and.

Axiom andI : forall (A B : prop), A -> B -> A /\ B.

Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.

(* Unicode \/ "2228" *)
Infix \/ 785 left := or.

Axiom xm : forall P:prop, P \/ ~P.

Section Eq.
Variable A:SType.
Definition eq : A->A->prop := fun x y:A => forall Q:A->A->prop, Q x y -> Q y x.
End Eq.

Infix = 502 := eq.

Section Ex.
Variable A:SType.
Definition ex : (A->prop)->prop := fun Q:A->prop => forall P:prop, (forall x:A, Q x -> P) -> P.
End Ex.

(* Unicode exists "2203" *)

Parameter In:set->set->prop.

Definition Subq : set -> set -> prop := fun A B => forall x :e A, x :e B.

Binder+ exists , := ex; and.

Axiom set_ext : forall X Y:set, X c= Y -> Y c= X -> X = Y.

Definition nIn : set->set->prop :=
fun x X => ~In x X.

(* Unicode /:e "2209" *)
Infix /:e 502 := nIn.

(* Parameter setminus "cc569397a7e47880ecd75c888fb7c5512aee4bcb1e7f6bd2c5f80cccd368c060" "c68e5a1f5f57bc5b6e12b423f8c24b51b48bcc32149a86fc2c30a969a15d8881" *)
Parameter setminus:set->set->set.

(* Unicode :\: "2216" *)
Infix :\: 350 := setminus.

Axiom setminusI:forall X Y z, (z :e X) -> (z /:e Y) -> z :e X :\: Y.
Axiom setminusE:forall X Y z, (z :e X :\: Y) -> z :e X /\ z /:e Y.
Axiom setminusE1:forall X Y z, (z :e X :\: Y) -> z :e X.

Theorem setminus_antimonotone : forall A U V, U c= V -> A :\: V c= A :\: U.
Admitted.

Parameter Repl : set -> (set -> set) -> set.
Notation Repl Repl.

Axiom ReplI : forall A:set, forall F:set->set, forall x:set, x :e A -> F x :e {F x|x :e A}.
Axiom ReplE : forall A:set, forall F:set->set, forall y:set, y :e {F x|x :e A} -> exists x :e A, y = F x.
Axiom ReplE_impred : forall A:set, forall F:set->set, forall y:set, y :e {F x|x :e A} -> forall p:prop, (forall x:set, x :e A -> y = F x -> p) -> p.

Theorem image_monotone : forall f:set -> set, forall U V, U c= V -> {f x|x :e U} c= {f x|x :e V}.
Admitted.

(* Unicode Power "1D4AB" *)
Parameter Power : set->set.

Axiom PowerI : forall X Y:set, Y c= X -> Y :e Power X.
Axiom PowerE : forall X Y:set, Y :e Power X -> Y c= X.

Theorem image_In_Power : forall A B, forall f:set -> set, (forall x :e A, f x :e B) -> forall U :e Power A, {f x|x :e U} :e Power B.
Admitted.

(* Parameter Sep "f7e63d81e8f98ac9bc7864e0b01f93952ef3b0cbf9777abab27bcbd743b6b079" "f336a4ec8d55185095e45a638507748bac5384e04e0c48d008e4f6a9653e9c44" *)
Parameter Sep:set -> (set -> prop) -> set.

Notation Sep Sep.

Axiom SepI:forall X:set, forall P:(set->prop), forall x:set, x :e X -> P x -> x :e {x :e X|P x}.
Axiom SepE1:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> x :e X.
Axiom SepE2:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> P x.
Axiom Sep_In_Power : forall X:set, forall P:set->prop, {x :e X|P x} :e Power X.
Axiom setminus_In_Power : forall A U, A :\: U :e Power A.

Theorem KnasterTarski_set: forall A, forall Phi:set->set,
    (forall U :e Power A, Phi U :e Power A)
 -> (forall U V :e Power A, U c= V -> Phi U c= Phi V)
 -> exists Y :e Power A, Phi Y = Y.
let A Phi.
assume H1: forall U :e Power A, Phi U :e Power A.
assume H2: forall U V :e Power A, U c= V -> Phi U c= Phi V.
prove exists Y :e Power A, Phi Y = Y.
set Y : set := {u :e A|forall X :e Power A, Phi X c= X -> u :e X}.
claim L1: Y :e Power A.
{ apply Sep_In_Power. }
claim L2: Phi Y :e Power A.
{ exact H1 Y L1. }
claim L3: forall X :e Power A, Phi X c= X -> Y c= X.
{ let X. assume HX: X :e Power A.
  assume H3: Phi X c= X.
  let y. assume Hy: y :e Y.
  prove y :e X.
  claim L3a: forall X :e Power A, Phi X c= X -> y :e X.
  { exact SepE2 A (fun u => forall X :e Power A, Phi X c= X -> u :e X) y Hy. }
  exact L3a X HX H3.
}
claim L4: Phi Y c= Y.
{ let u. assume H3: u :e Phi Y. prove u :e Y.
  apply SepI.
  - prove u :e A. exact PowerE A (Phi Y) L2 u H3.
  - admit. (** fill in this subproof **)
}
prove exists Y :e Power A, Phi Y = Y.
witness Y.
prove Y :e Power A /\ Phi Y = Y.
apply andI.
- exact L1.
- apply set_ext.
  + prove Phi Y c= Y.
    exact L4.
  + prove Y c= Phi Y. apply L3.
    * prove Phi Y :e Power A. exact L2.
    * prove Phi (Phi Y) c= Phi Y.
      admit. (** fill in this subproof **)
Qed.

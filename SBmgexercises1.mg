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
let A U V. assume HUV: U c= V.
let x. assume Hx: x :e A :\: V.
prove x :e A :\: U.
apply setminusE A V x Hx.
prove x :e A -> x /:e V -> x :e A :\: U.
assume H1: x :e A.
assume H2: x /:e V.
prove x :e A :\: U.
apply setminusI.
- prove x :e A.
  exact H1.
- prove x /:e U.
  assume H3: x :e U.
  prove False.
  apply H2.
  prove x :e V.
  exact HUV x H3.
Qed.

Parameter Repl : set -> (set -> set) -> set.
Notation Repl Repl.

Axiom ReplI : forall A:set, forall F:set->set, forall x:set, x :e A -> F x :e {F x|x :e A}.
Axiom ReplE : forall A:set, forall F:set->set, forall y:set, y :e {F x|x :e A} -> exists x :e A, y = F x.
Axiom ReplE_impred : forall A:set, forall F:set->set, forall y:set, y :e {F x|x :e A} -> forall p:prop, (forall x:set, x :e A -> y = F x -> p) -> p.

Theorem image_monotone : forall f:set -> set, forall U V, U c= V -> {f x|x :e U} c= {f x|x :e V}.
let f U V.
assume HUV: U c= V.
let y.
assume Hy: y :e {f x|x :e U}.
prove y :e {f x|x :e V}.
apply ReplE_impred U f y Hy.
prove forall x:set, x :e U -> y = f x -> y :e {f x|x :e V}.
let x.
assume Hx: x :e U.
assume H1: y = f x.
prove y :e {f x|x :e V}.
rewrite H1.
prove f x :e {f x|x :e V}.
apply ReplI V f x.
prove x :e V.
exact HUV x Hx.
Qed.

(* Unicode Power "1D4AB" *)
Parameter Power : set->set.

Axiom PowerI : forall X Y:set, Y c= X -> Y :e Power X.
Axiom PowerE : forall X Y:set, Y :e Power X -> Y c= X.

Theorem image_In_Power : forall A B, forall f:set -> set, (forall x :e A, f x :e B) -> forall U :e Power A, {f x|x :e U} :e Power B.
let A B f.
assume Hf: forall x :e A, f x :e B.
let U.
assume HU: U :e Power A.
prove {f x|x :e U} :e Power B.
apply PowerI.
prove {f x|x :e U} c= B.
let fx.
prove fx :e {f x|x :e U} -> fx :e B.
assume Hfx: fx :e {f x|x :e U}.
prove fx :e B.
apply ReplE_impred U f fx Hfx.
prove forall x:set, x :e U -> fx = f x -> fx :e B.
let x.
assume HxU: x :e U.
assume Hfxfx: fx = f x.
prove fx :e B.
rewrite Hfxfx.
prove f x :e B.
apply Hf x.
prove x :e A.
exact PowerE A U HU x HxU.
Qed.

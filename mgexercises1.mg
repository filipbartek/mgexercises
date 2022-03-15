Definition True : prop := forall p:prop, p -> p.
Definition False : prop := forall p:prop, p.

Theorem FalseE: forall A:prop, False -> A.
let A.
prove False -> A.
assume H: False.
prove A.
apply H.
Qed.

Definition not : prop -> prop := fun A:prop => A -> False.

(* Unicode ~ "00ac" *)
Prefix ~ 700 := not.

Theorem notE: forall A:prop, not A -> A -> False.
let A.
prove not A -> A -> False.
assume HnA: not A.
assume HA: A.
prove False.
apply HnA.
prove A.
exact HA.
Qed.

Theorem notI: forall A:prop, ( A -> False) -> not A.
let A.
assume HAF: A -> False.
prove not A.
exact HAF.
Qed.

Definition and : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> B -> p) -> p.

(* Unicode /\ "2227" *)
Infix /\ 780 left := and.

Theorem andEL : forall A B:prop, A /\ B -> A.
let A B.
assume HAB: A /\ B.
prove A.
apply HAB.
prove A -> B -> A.
assume HA HB.
exact HA.
Qed.

Theorem andER : forall A B:prop, A /\ B -> B.
let A B.
assume HAB: A /\ B.
prove B.
apply HAB.
prove A -> B -> B.
assume HA HB.
exact HB.
Qed.

Theorem andI : forall (A B : prop), A -> B -> A /\ B.
let A B.
assume HA HB.
prove A /\ B.
let p.
assume HABp: A -> B -> p.
prove p.
exact HABp HA HB.
Qed.

Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.

(* Unicode \/ "2228" *)
Infix \/ 785 left := or.

Theorem orE : forall A B C:prop, A \/ B -> (A -> C) -> (B -> C) -> C.
let A B C.
assume HAB: A \/ B.
assume HAC: A -> C.
assume HBC: B -> C.
prove C.
apply HAB.
- prove (A -> C).
  exact HAC.
- prove (B -> C).
  exact HBC.
Qed.

Theorem orIL : forall A B:prop, A -> A \/ B.
let A B.
assume HA: A.
prove A \/ B.
let p.
assume HAp: A -> p.
assume HBp: B -> p.
prove p.
exact HAp HA.
Qed.

Theorem orIR : forall A B:prop, B -> A \/ B.
let A B.
assume HB: B.
prove A \/ B.
let p.
assume HAp: A -> p.
assume HBp: B -> p.
prove p.
exact HBp HB.
Qed.

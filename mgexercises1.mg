Definition True : prop := forall p:prop, p -> p.
Definition False : prop := forall p:prop, p.

Theorem FalseE: forall A:prop, False -> A.
admit. (** fill in this proof **)
Qed.

Definition not : prop -> prop := fun A:prop => A -> False.

(* Unicode ~ "00ac" *)
Prefix ~ 700 := not.

Theorem notE: forall A:prop, not A -> A -> False.
admit. (** fill in this proof **)
Qed.

Theorem notI: forall A:prop, ( A -> False) -> not A.
admit. (** fill in this proof **)
Qed.

Definition and : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> B -> p) -> p.

(* Unicode /\ "2227" *)
Infix /\ 780 left := and.

Theorem andEL : forall A B:prop, A /\ B -> A.
admit. (** fill in this proof **)
Qed.

Theorem andER : forall A B:prop, A /\ B -> B.
admit. (** fill in this proof **)
Qed.

Theorem andI : forall (A B : prop), A -> B -> A /\ B.
admit. (** fill in this proof **)
Qed.

Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.

(* Unicode \/ "2228" *)
Infix \/ 785 left := or.

Theorem orE : forall A B C:prop, A \/ B -> (A -> C) -> (B -> C) -> C.
admit. (** fill in this proof **)
Qed.

Theorem orIL : forall A B:prop, A -> A \/ B.
admit. (** fill in this proof **)
Qed.

Theorem orIR : forall A B:prop, B -> A \/ B.
admit. (** fill in this proof **)
Qed.

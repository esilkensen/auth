Require Import PreLattice.

Definition unit_leq (x y: unit) := True.

Instance unit_PreOrder : PreOrder unit_leq.
Proof.
unfold unit_leq; constructor; auto.
Qed.

Instance unit_JoinPreLattice : JoinPreLattice unit unit_leq :=
{ join x y := x }.
Proof.
* unfold unit_leq. auto.
* unfold unit_leq. auto.
* unfold unit_leq. auto.
Defined.

Instance unit_MeetPreLattice : MeetPreLattice unit unit_leq :=
{ meet x y := x }.
Proof.
* unfold unit_leq. auto.
* unfold unit_leq. auto.
* unfold unit_leq. auto.
Defined.

Instance unit_HasBottom : HasBottom unit unit_leq :=
{ bottom := tt }.
Proof.
unfold unit_leq. auto.
Defined.

Instance unit_HasTop : HasTop unit unit_leq :=
{ top := tt }.
Proof.
unfold unit_leq. auto.
Defined.

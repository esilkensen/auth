Require Import LabelAlgebra.
Require Import UnitLattice.

Inductive two := Bottom2 | Top2.

Definition two_leq (x y: two) :=
  match x, y with
    | Bottom2, _ => True
    | Top2, Bottom2 => False
    | Top2, Top2 => True
  end.

Instance two_PreOrder : PreOrder two_leq.
Proof.
unfold two_leq; constructor.
* intros x. destruct x; auto.
* intros x y z Hxy Hyz.
  destruct x; auto.
  destruct y; auto.
Qed.

Instance two_JoinPreLattice : JoinPreLattice two two_leq :=
{ join x y :=
    match x, y with
      | Top2, _ | _, Top2 => Top2
      | Bottom2, Bottom2 => Bottom2
    end
}.
Proof.
* unfold two_leq. intros t1 t2; destruct t1; destruct t2; auto.
* unfold two_leq. intros t1 t2; destruct t2; auto. destruct t1; auto.
* unfold two_leq. intros t1 t2 t3 H12 H23.
  destruct t2; auto. destruct t3; auto.
Defined.

Instance two_MeetPreLattice : MeetPreLattice two two_leq :=
{ meet x y :=
    match x, y with
      | Bottom2, _ | _, Bottom2 => Bottom2
      | Top2, Top2 => Top2
    end
}.
Proof.
* unfold two_leq. intros t1 t2; destruct t1; destruct t2; auto.
* unfold two_leq. intros t1 t2; destruct t1; auto. destruct t2; auto.
* unfold two_leq. intros t1 t2 t3 H12 H23.
  destruct t2; auto. destruct t3; auto.
Defined.

Instance two_HasBottom : HasBottom two two_leq :=
{ bottom := Bottom2 }.
Proof.
unfold two_leq. auto.
Defined.

Instance two_HasTop : HasTop two two_leq :=
{ top := Top2 }.
Proof.
unfold two_leq. intros t; destruct t; trivial.
Defined.

Instance Two : LabelAlgebra unit two :=
{ Ldef := Bottom2
; labLeq := two_leq
; authLeq := unit_leq
; flowsTo a := two_leq
}.
Proof.
* split; intros x y; tauto.
* auto.
* auto.
* intros t1 t2 H x. tauto.
Defined.

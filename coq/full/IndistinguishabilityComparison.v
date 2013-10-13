Require Import MyTactics.
Require Import LabelAlgebra.
Require Import Lambda.
Require Import BooleanIndistinguishability.
Require Import Indistinguishability.

Set Implicit Arguments.

(** * Comparison of indistinguishability and indistinguishability of booleans. *)
Section Comparison.

Context {A L: Type} {LA: LabelAlgebra A L}.

Lemma bool_Lequiv_Lequiv (auth: A) (lab: L) :
  forall a1 a2 : atom A L,
    bool_Lequiv auth lab a1 a2 ->
    atom_Lequiv auth lab a1 a2.
Proof.
intros [v1 l1] [v2 l2] H.
simpl in H. destruct v1; destruct v2; try tauto. auto.
Qed.

Lemma bool_env_Lequiv_env_Lequiv (auth: A) (lab: L) :
  forall e1 e2 : env A L,
    bool_env_Lequiv auth lab e1 e2 ->
    env_Lequiv auth lab e1 e2.
Proof.
intros e1 e2 H.
apply (list_forall2_inclusion (bool_Lequiv auth lab) _
                              (bool_Lequiv_Lequiv auth lab) _ _ H).
Qed.

Lemma bool_Lequiv_iff_Lequiv (auth: A) (lab: L) :
  forall a1 a2 : atom A L,
    bool_Lequiv auth lab a1 a2 <->
    (atom_Lequiv auth lab a1 a2
     /\ exists b1 b2 l1 l2, a1 = Atom (VBool b1) l1 /\ a2 = Atom (VBool b2) l2).
Proof.
intros a1 a2. split; intro H.
* destruct a1 as [v1 l1]. destruct a2 as [v2 l2]. simpl in H.
  destruct v1; destruct v2; try tauto. split; eauto 6.
* destruct H as [H [b1 [b2 [l1 [l2 [H1 H2]]]]]].
  subst. intro Hlab. specialize (H Hlab). simpl in H.
  clear Hlab. intuition auto. split; assumption.
Qed.

End Comparison.

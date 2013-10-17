Require Import Program.Tactics.
Require Import MyTactics.
Require Import LabelAlgebra.
Require Import LambdaTwo.
Require Import TermEquivTwo.
Require Import IndistinguishabilityTwo.

Set Implicit Arguments.

Section NI.

Context (L : two)
        (P : value -> value -> Prop)
        (Pv : forall v1 v2, value_Lequiv L P v1 v2 -> P v1 v2).
  
(** * Preliminary lemmas. *)
(** ** The pc label is below the label of the resulting atom. *)
Lemma eval_pc_lower_bound :
  forall pc e t v l,
    pc; e ⊢ t ⇓ Atom v l ->
    pc ⊑ l.
Proof.
  intros pc e t v l Heval.
  remember (Atom v l) as a.
  generalize dependent l. generalize dependent v.
  induction Heval; intros v' l' Heq; inversion Heq; subst; auto.
  destruct l; destruct pc; reflexivity.
  transitivity l1. 
    apply (IHHeval1 (VClos e1' t1') l1). reflexivity.
    apply (IHHeval3 v' l'). reflexivity.
Qed.

Lemma join_top :
  forall l, l ⊔ Top2 = Top2.
Proof. destruct l; reflexivity. Qed.

Lemma join_bot :
  forall l, l ⊔ Bottom2 = l.
Proof. destruct l; reflexivity. Qed.

(** ** Strong version of the non-interference theorem. *)
Lemma NI_strong :
  forall pc1 pc2 e1 e2 t1 t2 a1 a2,
    pc1 = pc2 ->
    env_Lequiv L P e1 e2 ->
    term_equiv t1 t2 ->
    pc1; e1 ⊢ t1 ⇓ a1 ->
    pc2; e2 ⊢ t2 ⇓ a2 ->
    atom_Lequiv L P a1 a2.
Proof.
  intros pc1 pc2 e1 e2 t1 t2 a1 a2 Hpc He Ht Heval.
  generalize dependent a2.
  generalize dependent t2.
  generalize dependent e2.
  generalize dependent pc2.
  induction Heval;
    intros pc2 Hpc e2 He t2' Ht a2' Heval2'; destruct t2'; try inversion Ht.
    (* Eval_nat *)
    inversion Heval2'. subst.
    destruct L; destruct pc2.
      right. left. auto.
      left. auto.
      right. right. auto.
      right. right. auto.
    (* Eval_var *)
    inversion Heval2'. subst. unfold env_Lequiv in He.
    assert (atom_Lequiv L P (Atom v l) (Atom v0 l0)) by
        (eapply list_forall2_atIndex; eassumption).
    assert (l = l0) by
        (eapply atom_Lequiv_lab_inv; eassumption).
    subst.
    destruct pc2.
      rewrite join_bot. assumption.
      rewrite join_top. destruct l0.
        apply atom_Lequiv_raise. apply Pv. assumption. assumption.
    (* Eval_lam *)
    inversion Heval2'. subst.
    destruct L; destruct pc2.
      right. left. auto.
      left. auto.
      right. right. auto.
      right. right. auto.
    (* Eval_app *)
    Admitted.
    

(** * General non-interference theorem. *)
Theorem general_non_interference :
  forall pc e1 e2 t a1 a2,
    env_Lequiv L P e1 e2 ->
    pc; e1 ⊢ t ⇓ a1 ->
    pc; e2 ⊢ t ⇓ a2 ->
    atom_Lequiv L P a1 a2.
Proof.
  Admitted.

End NI.

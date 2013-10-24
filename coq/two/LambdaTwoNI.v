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
        (Prefl : forall x, P x x).
  
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

(** ** Strong version of the non-interference theorem. *)
Lemma NI_strong :
  forall pc1 pc2 e1 e2 t1 t2 a1 a2,
    pc1 = pc2 ->
    env_LPequiv L P e1 e2 ->
    term_equiv t1 t2 ->
    pc1; e1 ⊢ t1 ⇓ a1 ->
    pc2; e2 ⊢ t2 ⇓ a2 ->
    atom_Lequiv L a1 a2.
Proof.
  intros pc1 pc2 e1 e2 t1 t2 a1 a2 Hpc He Ht Heval.
  generalize dependent a2.
  generalize dependent t2.
  generalize dependent e2.
  generalize dependent pc2.
  induction Heval;
    intros pc2 Hpc e2 He t2' Ht a3' Heval2'; destruct t2'; try inversion Ht.
  - (* Eval_nat *)
    inversion Heval2'. subst.
    destruct L; destruct pc2.
      right. left. auto.
      left. auto.
      right. right. auto.
      right. right. auto.
  - (* Eval_var *)
    inversion Heval2'. subst. unfold env_LPequiv in He.
    assert (atom_LPequiv L P (Atom v l) (Atom v0 l0)) by
        (eapply list_forall2_atIndex; eassumption).
    assert (l = l0) by
        (eapply atom_LPequiv_lab_inv; eassumption).
    subst.
    destruct pc2.
      rewrite join_bot. eapply atom_LPequiv_Lequiv. eassumption.
      rewrite join_top. destruct l0.
        apply atom_LPequiv_raise in H0. eapply atom_LPequiv_Lequiv. eassumption.
          assumption.
        eapply atom_LPequiv_Lequiv. eassumption.
  - (* Eval_lam *)
    inversion Heval2'. subst.
    apply env_LPequiv_Lequiv in He.
    destruct L; destruct pc2.
      right. left. auto. 
      left. auto.
      right. right. auto.
      right. right. auto.
  - (* Eval_app *)
    inversion Heval2'. subst.
    rename l0 into l1'. rename a0 into a2'.
    assert (t2'1 = t1) by
        (apply term_equiv_eq; symmetry; auto).
    assert (t2'2 = t2) by
        (apply term_equiv_eq; symmetry; auto).
    subst. clear H. clear H0. clear Ht.
    assert (l1' = l1).
      apply IHHeval1 in H3. apply atom_LPequiv_lab_inv in H3.
        symmetry. assumption. reflexivity. assumption. reflexivity. subst.
    destruct a3 as [v3 l3]; destruct a3' as [v3' l3'].
    apply IHHeval1 in H3.
    apply IHHeval2 in H6. {
      destruct L; destruct l3; destruct l3'.
      + (* Bottom2, Bottom2, Bottom2 *)
        admit.
      + (* Bottom2, Bottom2, Top2 *)
        destruct l1.
          admit. (* Bottom2 *)
          apply eval_pc_lower_bound in Heval3. inversion Heval3.
      + (* Bottom2, Top2, Bottom2 *)
        destruct l1.
          admit. (* Bottom2 *)
          apply eval_pc_lower_bound in H8. inversion H8.
      + (* Bottom2, Top2, Top2 *)
        destruct v3; destruct v3'; left; auto.
      + (* Top2, Bottom2, Bottom2 *)
        destruct l1.
          destruct H3; destruct H; destruct_conjs; inversion H.
            admit. (* Bottom2 *)
          apply eval_pc_lower_bound in H8. inversion H8.
      + (* Top2, Bottom2, Top2 *)
        destruct l1.
          admit. (* Bottom2 *)
          apply eval_pc_lower_bound in Heval3. inversion Heval3.
      + (* Top2, Top2, Bottom2 *)
        destruct l1.
          admit. (* Bottom2 *)
          apply eval_pc_lower_bound in H8. inversion H8.
      + (* Top2, Top2, Top2 *)
        admit.
    }
    reflexivity. assumption. reflexivity.
    reflexivity. assumption. reflexivity.
Qed.
      
(** * General non-interference theorem. *)
Theorem general_non_interference :
  forall pc e1 e2 t a1 a2,
    env_LPequiv L P e1 e2 ->
    pc; e1 ⊢ t ⇓ a1 ->
    pc; e2 ⊢ t ⇓ a2 ->
    atom_Lequiv L a1 a2.
Proof. intros. eapply NI_strong; eauto. Qed.

End NI.

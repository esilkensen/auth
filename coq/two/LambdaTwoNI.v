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
    intros pc2 Hpc e2 He t2' Ht a3' Heval2'; destruct t2'; try inversion Ht.
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
        apply atom_Lequiv_raise. apply Prefl. assumption. assumption.
    (* Eval_lam *)
    inversion Heval2'. subst.
    destruct L; destruct pc2.
      right. left. auto.
      left. auto.
      right. right. auto.
      right. right. auto.
    (* Eval_app *)
    inversion Heval2'. subst.
    rename l0 into l1'. rename a0 into a2'.
    assert (t2'1 = t1) by
        (apply term_equiv_eq; symmetry; auto).
    assert (t2'2 = t2) by
        (apply term_equiv_eq; symmetry; auto).
    subst. clear H. clear H0. clear Ht.
    remember (Atom (VClos e1' t1') l1) as f1.
    remember (Atom (VClos e1'0 t1'0) l1') as f2.
    assert (atom_Lequiv L P f1 f2) by
        (eapply IHHeval1; eauto). subst.
    assert (l1' = l1) by
        (apply atom_Lequiv_lab_inv in H; auto). subst.
    destruct L.
      destruct l1.
        destruct H; destruct H; destruct_conjs; try inversion H1; inversion H.
          assert (atom_Lequiv Bottom2 P a2 a2').
            apply IHHeval2 in H6; auto.
          assert (env_Lequiv Bottom2 P e1' e1'0) by auto.
          assert (env_Lequiv Bottom2 P (a2 :: e1') (a2' :: e1'0)).
            split; auto. 
          apply IHHeval3 in H8; auto.
        destruct a3 as [v3 l3]; destruct v3; destruct l3;
        destruct a3' as [v3' l3']; destruct v3'; destruct l3';
          apply eval_pc_lower_bound in H8; inversion H8;
          apply eval_pc_lower_bound in Heval3; inversion Heval3;
          left; auto; repeat (split; auto).
        admit. (* TODO: L=Bottom2 l1=Top2, need P (VNat n) (VNat n0) *)
      assert (env_Lequiv Top2 P e1' e1'0) by
            (destruct H; destruct H; destruct_conjs; inversion H; auto).
      assert (atom_Lequiv Top2 P a2 a2') by
            (apply IHHeval2 in H6; auto).
      assert (env_Lequiv Top2 P (a2 :: e1') (a2' :: e1'0)) by
          (split; auto).
      assert (term_equiv t1' t1'0) by
          (destruct H; destruct H; destruct_conjs; inversion H; auto).
      apply IHHeval3 in H8; auto.
Qed.
      
(** * General non-interference theorem. *)
Theorem general_non_interference :
  forall pc e1 e2 t a1 a2,
    env_Lequiv L P e1 e2 ->
    pc; e1 ⊢ t ⇓ a1 ->
    pc; e2 ⊢ t ⇓ a2 ->
    atom_Lequiv L P a1 a2.
Proof. intros. eapply NI_strong; eauto. Qed.

End NI.

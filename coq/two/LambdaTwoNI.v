Require Import Program.Tactics.
Require Import LambdaTwo.

Section NI.

Context (L : two).

(** * Preliminary lemmas. *)
(** ** The pc label is below the label of the resulting atom. *)
Lemma eval_pc_lower_bound :
  forall P pc e t v l,
    P, pc; e ⊢ t ⇓ Atom v l ->
    pc ⊑ l.
Proof.
  intros P pc e t v l Heval.
  remember (Atom v l) as a.
  generalize dependent l. generalize dependent v.
  induction Heval; intros v' l' Heq; inversion Heq; subst; auto.
  destruct l; destruct pc; reflexivity.
  transitivity l1. 
    apply (IHHeval1 (VClos e1' t1') l1). reflexivity.
    apply (IHHeval3 v' l'). reflexivity.
  apply (IHHeval v'). reflexivity.
Qed.

(** * General non-interference theorem. *)
Theorem general_non_interference :
  forall (P : value -> value -> Prop) pc e1 e2 t a1 a2,
    (forall x, P x x) ->
    env_LPequiv L P e1 e2 ->
    P, pc; e1 ⊢ t ⇓ a1 ->
    P, pc; e2 ⊢ t ⇓ a2 ->
    atom_Lequiv L a1 a2.
Proof. 
  intros P pc e1 e2 t a1 a2 Prefl He Heval.
  generalize dependent a2.
  generalize dependent e2.
  induction Heval; intros e2 He a3' Heval2'; inversion Heval2'; subst.
  - (* Eval_nat *)
    destruct L; destruct pc.
      right. left. auto.
      left. auto.
      right. right. auto.
      right. right. auto.
  - (* Eval_var *)
    unfold env_LPequiv in He.
    assert (atom_LPequiv L P (Atom v l) (Atom v0 l0)) by
        (eapply list_forall2_atIndex; eassumption).
    assert (l = l0) by
        (eapply atom_LPequiv_lab_inv; eassumption).
    symmetry in H1. subst.
    destruct pc.
      rewrite join_bot. eapply atom_LPequiv_Lequiv. eassumption.
      rewrite join_top. destruct l.
        apply atom_LPequiv_raise in H0. eapply atom_LPequiv_Lequiv. eassumption.
          assumption.
        eapply atom_LPequiv_Lequiv. eassumption.
  - (* Eval_lam *)
    apply env_LPequiv_Lequiv in He.
    destruct L; destruct pc.
      right. left. auto. 
      left. auto.
      right. right. auto.
      right. right. auto.
  - (* Eval_app *)
    rename l0 into l1'. rename a0 into a2'. 
    assert (l1' = l1).
      apply IHHeval1 in H1. apply atom_LPequiv_lab_inv in H1.
        symmetry. assumption. assumption. assumption. subst.
    destruct a3 as [v3 l3]; destruct a3' as [v3' l3'].
    apply IHHeval1 in H1. apply IHHeval2 in H5. {
      destruct L; destruct l1.
      + (* Bottom2, Bottom2 *)
        assert (t1'0 = t1' /\ env_Lequiv Bottom2 e1' e1'0) by
            (split; destruct H1; destruct H; destruct_conjs;
             try inversion H1; subst; auto). destruct_conjs. subst.
        apply IHHeval3 with (e2 := a2' :: e1'0); auto.
        split; apply atom_value_env_Lequiv_LPequiv; assumption.
      + (* Bottom2, Top2 *)
        destruct l3; destruct l3';
        apply eval_pc_lower_bound in H7; inversion H7;
        apply eval_pc_lower_bound in Heval3; inversion Heval3.
        destruct v3; destruct v3'; left; auto.
      + (* Top2, Bottom2 *)
        assert (t1'0 = t1' /\ env_Lequiv Top2 e1' e1'0) by
            (split; destruct H1; destruct H; destruct_conjs;
             try inversion H1; subst; auto). destruct_conjs. subst.
        apply IHHeval3 with (e2 := a2' :: e1'0); auto.
        split; apply atom_value_env_Lequiv_LPequiv; assumption.
      + (* Top2, Top2 *)
        destruct l3; destruct l3'.
        apply eval_pc_lower_bound in H7; inversion H7.
        apply eval_pc_lower_bound in Heval3. inversion Heval3.
        apply eval_pc_lower_bound in H7; inversion H7.
        assert (t1'0 = t1' /\ env_Lequiv Top2 e1' e1'0) by
            (split; destruct H1; destruct H; destruct_conjs;
             try inversion H; subst; auto). destruct_conjs. subst.
        apply IHHeval3 with (e2 := a2' :: e1'0); auto.
        split; apply atom_value_env_Lequiv_LPequiv; assumption.
    } assumption. assumption. assumption. assumption.
  - (* Eval_decl1 *) 
    eapply IHHeval; eauto.
Qed.

End NI.

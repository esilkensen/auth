Require Import Program.Tactics.
Require Import LambdaTwo.

Section NI.

Context (L : two).
  
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
  induction Heval; intros e2 He a3' Heval2'.
  - (* Eval_nat *)
    inversion Heval2'. subst.
    destruct L; destruct pc.
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
    destruct pc.
      rewrite join_bot. eapply atom_LPequiv_Lequiv. eassumption.
      rewrite join_top. destruct l0.
        apply atom_LPequiv_raise in H0. eapply atom_LPequiv_Lequiv. eassumption.
          assumption.
        eapply atom_LPequiv_Lequiv. eassumption.
  - (* Eval_lam *)
    inversion Heval2'. subst.
    apply env_LPequiv_Lequiv in He.
    destruct L; destruct pc.
      right. left. auto. 
      left. auto.
      right. right. auto.
      right. right. auto.
  - (* Eval_app *)
    inversion Heval2'. subst.
    rename l0 into l1'. rename a0 into a2'. 
    assert (l1' = l1).
      apply IHHeval1 in H1. apply atom_LPequiv_lab_inv in H1.
        symmetry. assumption. assumption. assumption. subst.
    destruct a3 as [v3 l3]; destruct a3' as [v3' l3'].
    apply IHHeval1 in H1.
    apply IHHeval2 in H5. {
      destruct L; destruct l3; destruct l3'.
      + (* Bottom2, Bottom2, Bottom2 *)
        admit.
      + (* Bottom2, Bottom2, Top2 *)
        admit.
      + (* Bottom2, Top2, Bottom2 *)
        admit.
      + (* Bottom2, Top2, Top2 *)
        destruct v3; destruct v3'; left; auto.
      + (* Top2, Bottom2, Bottom2 *)
        admit.
      + (* Top2, Bottom2, Top2 *)
        admit.
      + (* Top2, Top2, Bottom2 *)
        admit.
      + (* Top2, Top2, Top2 *)
        admit.
    } assumption. assumption. assumption. assumption.
  - (* Eval_decl1 *)
    admit.
  - (* Eval_decl2 *)
    admit.
Qed.

End NI.

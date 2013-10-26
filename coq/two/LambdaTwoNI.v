Require Import Program.Tactics.
Require Import LambdaTwo.

Section NI.

Lemma non_interference_top :
  forall (P : value -> value -> Prop) pc e1 e2 t a1 a2,
    (forall x, P x x) ->
    env_Lequiv Top2 e1 e2 ->
    P, pc; e1 ⊢ t ⇓ a1 ->
    P, pc; e2 ⊢ t ⇓ a2 ->
    atom_Lequiv Top2 a1 a2.
Proof.
  intros P pc e1 e2 t a1 a2 Prefl He Heval.
  generalize dependent a2.
  generalize dependent e2.
  induction Heval; intros e2 He a3' Heval2'; inversion Heval2'; subst.
  - (* Eval_nat *)
    destruct pc; right; right; auto.
  - (* Eval_var *)
    rename e into e1.
    rename v into v1. rename l into l1.
    rename v0 into v2. rename l0 into l2.
    unfold env_Lequiv in He. unfold env_LPequiv in He.
    assert (atom_Lequiv Top2 (Atom v1 l1) (Atom v2 l2)) by
        (eapply list_forall2_atIndex; eassumption).
    assert (l2 = l1) by
        (unfold atom_Lequiv in H0; apply atom_LPequiv_lab_inv in H0;
         subst; reflexivity). subst.
    destruct pc; unfold atom_Lequiv in H0.
    + rewrite join_bot. eapply atom_LPequiv_Lequiv. eassumption.
    + rewrite join_top. destruct l1; auto.
      eapply atom_LPequiv_raise; eauto.
  - (* Eval_lam *)
    rename e into e1. 
    unfold env_Lequiv in He. 
    apply env_LPequiv_Lequiv in He.
    destruct pc; right; right; auto.
  - (* Eval_app *)
    admit.
  - (* Eval_decl1 *)
    rename v into v1. rename v0 into v2. rename e into e1.
    eapply IHHeval; eauto.
Qed.

Lemma non_interference_bot :
  forall (P : value -> value -> Prop) pc e1 e2 t a1 a2,
    (forall x, P x x) ->
    env_LPequiv Bottom2 P e1 e2 ->
    P, pc; e1 ⊢ t ⇓ a1 ->
    P, pc; e2 ⊢ t ⇓ a2 ->
    atom_Lequiv Bottom2 a1 a2.
Proof.
  intros P pc e1 e2 t a1 a2 Prefl He Heval.
  generalize dependent a2.
  generalize dependent e2.
  induction Heval; intros e2 He a3' Heval2'; inversion Heval2'; subst.
  - (* Eval_nat *)
    destruct pc; [right; left; auto | left; auto].
  - (* Eval_var *)
    rename e into e1.
    rename v into v1. rename l into l1.
    rename v0 into v2. rename l0 into l2.
    unfold env_LPequiv in He.
    assert (atom_LPequiv Bottom2 P (Atom v1 l1) (Atom v2 l2)) by
        (eapply list_forall2_atIndex; eassumption).
    assert (l2 = l1) by
        (apply atom_LPequiv_lab_inv in H0; subst; reflexivity). subst.
    destruct pc.
    + rewrite join_bot. eapply atom_LPequiv_Lequiv. eassumption.
    + rewrite join_top. destruct l1.
      * apply atom_LPequiv_raise in H0.
          eapply atom_LPequiv_Lequiv. eassumption.
        assumption.
      * eapply atom_LPequiv_Lequiv. eassumption.
  - (* Eval_lam *)
    rename e into e1.
    apply env_LPequiv_Lequiv in He.
    destruct pc; [right; left; auto | left; auto].
  - (* Eval_app *)
    admit.
  - (* Eval_decl1 *)
    rename e into e1.
    rename v into v1. rename v0 into v2.
    eapply IHHeval; eauto.
Qed.

End NI.

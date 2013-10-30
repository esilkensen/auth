Require Import Program.Tactics.
Require Import LambdaTwo.

Section NI.

Theorem non_interference_strong_observer :
  forall L (P : value -> value -> Prop) k pc e1 e2 t a1 a2,
    (forall x, P x x) ->
    env_LPequiv L P e1 e2 ->
    [L, P, k] pc; e1 ⊢ t ⇓ a1 ->
    [L, P, k] pc; e2 ⊢ t ⇓ a2 ->
    atom_LPequiv L P a1 a2.
Proof.
  intros L P k pc e1 e2 t a1 a2 Prefl He Heval.
  generalize dependent a2.
  generalize dependent e2.
  induction Heval; intros e2 He a3' Heval2';
  inversion Heval2'; rename e into e1; subst.
  - (* E_Nat *) 
    destruct L; destruct pc.
    + right. left. auto.
    + left. auto.
    + right. right. auto.
    + right. right. auto.
  - (* E_Var *) 
    rename v into v1. rename l into l1.
    rename v0 into v2. rename l0 into l2.
    destruct pc.
    + rewrite 2! join_bot in *.
      eapply list_forall2_atIndex in H3; eauto.
    + rewrite 2! join_top in *.
      assert (atom_LPequiv L P (Atom v1 l1) (Atom v2 l2)) by
          (eapply list_forall2_atIndex; eassumption).
      assert (l2 = l1) by
          (apply atom_LPequiv_lab_inv in H0; subst; reflexivity).
      destruct l1; subst; auto.
      apply atom_LPequiv_raise; auto.
  - (* E_Abs *)
    destruct L; destruct pc.
    + right. left. auto.
    + left. auto.
    + right. right. auto.
    + right. right. auto.
  - (* E_App *)
    rename a0 into a2'.
    rename e1'0 into e2'. rename t1'0 into t2'. rename l0 into l2.
    destruct a3 as [v3 l3]; destruct a3' as [v3' l3'].
    apply IHHeval1 in H4.
    apply IHHeval2 in H7. {
      assert (l2 = l1) by
          (apply atom_LPequiv_lab_inv in H4; subst; reflexivity). subst.
      assert (t2' = t1' /\ env_LPequiv L P e1' e2') by
          (split; destruct H4; destruct H; destruct_conjs;
           try inversion H1; subst; auto).
      destruct_conjs; subst. eapply IHHeval3; eauto. split; assumption.
    } assumption. assumption. assumption. assumption.
  - (* E_Decl1 *)
    rename v into v1. rename v0 into v2. 
    eapply IHHeval; eauto.
Qed.

Theorem non_interference :
  forall L (P : value -> value -> Prop) k pc e1 e2 t a1 a2,
    (forall x, P x x) ->
    env_LPequiv L P e1 e2 ->
    [L, P, k] pc; e1 ⊢ t ⇓ a1 ->
    [L, P, k] pc; e2 ⊢ t ⇓ a2 ->
    atom_Lequiv L a1 a2.
Proof.
  intros.
  assert (atom_LPequiv L P a1 a2) by
      (eapply non_interference_strong_observer; eauto).
  eapply atom_LPequiv_Lequiv. eauto.
Qed.

End NI.

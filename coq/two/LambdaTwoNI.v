Require Import Program.Tactics.
Require Import LambdaTwo.

Section NI.

Theorem non_interference_strong_observer :
  forall L (P : value -> value -> Prop) pc e1 e2 t o1 o2 a1 a2,
    (forall x, P x x) ->
    env_LPequiv L P e1 e2 ->
    [L, P] pc; e1 ⊢ t ⇓ o1 ->
    [L, P] pc; e2 ⊢ t ⇓ o2 ->
    o1 = Some a1 ->
    o2 = Some a2 ->
    atom_LPequiv L P a1 a2.
Proof.
  intros L P pc e1 e2 t o1 o2 a1 a2 Prefl He Heval1 Heval2 Ha1 Ha2.
  generalize dependent a2.
  generalize dependent a1.
  generalize dependent o2.
  generalize dependent e2.
  induction Heval1; intros; rename e into e1; inversion Ha1; subst.
  - (* E_Nat *)
    inversion Heval2. subst.
    destruct L; destruct pc. 
    + right. left. auto.
    + left. auto.
    + right. right. auto.
    + right. right. auto.
  - (* E_Var *)
    inversion Heval2. subst.
    rename v into v1. rename l into l1.
    rename v0 into v2. rename l0 into l2.
    assert (atom_LPequiv L P (Atom v1 l1) (Atom v2 l2)) by
        (eapply list_forall2_atIndex; eauto).
    destruct pc; destruct l1; destruct l2; auto.
    + apply atom_LPequiv_raise; auto.
    + apply atom_LPequiv_lab_inv in H0. inversion H0.
    + apply atom_LPequiv_lab_inv in H0. inversion H0.
  - (* E_Abs *)
    inversion Heval2. subst.
    destruct L; destruct pc.
    + right. left. auto.
    + left. auto.
    + right. right. auto.
    + right. right. auto.
  - (* E_App *)
    inversion Heval2. subst.
    rename a0 into a3'.
    rename a3 into a2'.
    rename a1 into a3.
    rename e1'0 into e2'. rename t1'0 into t2'. rename l0 into l2.
    destruct a3 as [v3 l3]. destruct a3' as [v3' l3'].
    apply IHHeval1_1 with (a1 := (Atom (VClos e1' t1') l1))
                            (a2 := (Atom (VClos e2' t2') l2)) in H6.
    apply IHHeval1_2 with (a1 := a2) (a2 := a2') in H7.
    assert (l2 = l1) by
        (apply atom_LPequiv_lab_inv in H6; subst; reflexivity). subst.
    assert (t2' = t1' /\ env_LPequiv L P e1' e2') by
        (split; destruct H6; destruct H; destruct_conjs; subst; auto).
    destruct_conjs. subst. eapply IHHeval1_3; eauto. split; assumption.
    assumption. assumption. reflexivity. reflexivity.
    assumption. assumption. reflexivity. reflexivity.
  - (* E_Decl1 *)
    inversion Heval2; subst.
    + rename v into v1. rename v0 into v2.
      eapply IHHeval1; eauto.
    + rename v into v1. rename v3 into v2.
      assert (atom_LPequiv L P (Atom v1 Bottom2) (Atom v2 Top2)) by
          (apply IHHeval1 with (e2 := e2) (o2 := (Some (Atom v2 Top2)));
           auto; eapply E_App; eauto).
      apply atom_LPequiv_lab_inv in H. inversion H.
    + rename v into v1. rename v3 into v2.
      assert (atom_LPequiv L P (Atom v1 Bottom2) (Atom v2 Top2)) by
          (apply IHHeval1 with (e2 := e2) (o2 := (Some (Atom v2 Top2)));
           auto; eapply E_App; eauto).
      apply atom_LPequiv_lab_inv in H. inversion H.
  - (* E_Decl2 *)
    admit.
  - (* E_Decl2' *)
    admit.
Qed.

Theorem non_interference :
  forall L (P : value -> value -> Prop) pc e1 e2 t o1 o2 a1 a2,
    (forall x, P x x) ->
    env_LPequiv L P e1 e2 ->
    [L, P] pc; e1 ⊢ t ⇓ o1 ->
    [L, P] pc; e2 ⊢ t ⇓ o2 ->
    o1 = Some a1 ->
    o2 = Some a2 ->
    atom_Lequiv L a1 a2.
Proof.
  intros.
  assert (atom_LPequiv L P a1 a2) by
      (eapply non_interference_strong_observer; eauto).
  eapply atom_LPequiv_Lequiv. eauto.
Qed.

End NI.

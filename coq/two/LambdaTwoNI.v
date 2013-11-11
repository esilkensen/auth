Require Import Program.Tactics.
Require Import LambdaTwo.
Require Import LibTactics.

Section NI.

Theorem non_interference_strong_observer :
  forall L P pc e1 e2 t a1 a2,
    env_LPequiv L P e1 e2 ->
    P, pc; e1 ⊢ t ⇓ a1 ->
    P, pc; e2 ⊢ t ⇓ a2 ->
    atom_LPequiv L P a1 a2.
Proof.
  introv He Heval1 Heval2; gen e2 a2.
  induction Heval1; intros; rename e into e1.
  - (* E_Bool *)
    inversion Heval2; subst.
    destruct L; destruct pc.
    + right. left. auto.
    + left. auto.
    + right. right. auto.
    + right. right. auto.
  - (* E_Nat *)
    inversion Heval2; subst.
    destruct L; destruct pc.
    + right. left. auto.
    + left. auto.
    + right. right. auto.
    + right. right. auto.
  - (* E_Var *)
    inversion Heval2; subst;
    rename v into v1; rename l into l1;
    rename v0 into v2; rename l0 into l2.
    assert (Ha: atom_LPequiv L P (Atom v1 l1) (Atom v2 l2)) by
        (eapply list_forall2_atIndex; eauto).
    assert (l2 = l1) by (apply atom_LPequiv_lab_inv in Ha; auto); subst.
    destruct pc.
    + rewrite join_bot. assumption.
    + rewrite join_top. destruct l1; try assumption.
      apply atom_LPequiv_raise. assumption.
  - (* E_Abs *)
    inversion Heval2; subst.
    destruct L; destruct pc.
    + right. left. auto.
    + left. auto.
    + right. right. auto.
    + right. right. auto.
  - (* E_App *)
    inversion Heval2; subst;
    rename e1'0 into e1''; rename t1'0 into t1''; rename l0 into l1';
    rename a1 into a2'; rename a0 into a3';
    rename H1 into Heval2_1; rename H5 into Heval2_2; rename H7 into Heval2_3.
    remember (Atom (VClos e1' t1') l1) as a1;
    remember (Atom (VClos e1'' t1'') l1') as a1'.
    assert (Ha1: atom_LPequiv L P a1 a1') by (eapply IHHeval1_1; eauto); subst.
    assert (Ha2: atom_LPequiv L P a2 a2') by (eapply IHHeval1_2; eauto).
    assert (l1' = l1) by (apply atom_LPequiv_lab_inv in Ha1; auto); subst.
    assert (He1: t1'' = t1' /\ env_LPequiv L P e1' e1'') by
        (split; destruct Ha1; destruct H; destruct_conjs; subst; auto);
      destruct He1 as [Ht He1]; subst.
    assert (He': env_LPequiv L P (a2 :: e1') (a2' :: e1'')) by (split; auto).
    eapply IHHeval1_3; eauto.
  - (* E_Decl1 *)
    inversion Heval2; subst;
    rename n into n1; rename L0 into l1;
    rename n0 into n2; rename L1 into l2.
    + destruct L; right.
      * left. auto.
      * right. auto.
    + assert (Ha: atom_LPequiv L P (Atom (VNat n1) l1) (Atom (VNat n2) l2)) by
          (eapply IHHeval1; eauto).
      assert (l2 = l1) by (apply atom_LPequiv_lab_inv in Ha; auto); subst.
      destruct L;
        (destruct l1;
         try (assert (~ P n1) by
                 (destruct Ha; destruct H0; destruct_conjs;
                  inversion H3; subst; auto));
         try (assert (P n2) by
                 (destruct Ha; destruct H0; destruct_conjs; 
                  try rewrite <- H4; subst; auto));
         contradiction).
  - (* E_Decl2 *)
    inversion Heval2; subst;
    rename n into n1; rename L0 into l1;
    rename n0 into n2; rename L1 into l2;
    assert (Ha: atom_LPequiv L P (Atom (VNat n1) l1) (Atom (VNat n2) l2)) by
        (eapply IHHeval1; eauto);
    assert (l2 = l1) by (apply atom_LPequiv_lab_inv in Ha; auto); subst.
    + destruct L;
      (destruct l1;
       try (assert (P n1) by
               (destruct Ha; destruct H0; destruct_conjs;
                inversion H3; subst; auto));
       try (assert (P n1) by
               (destruct Ha; destruct H0; destruct_conjs;
                try rewrite H4; subst; auto));
       contradiction).
    + destruct L; destruct l1; right.
      * left. auto.
      * left. auto.
      * right. auto.
      * right. auto.
Qed.

Theorem non_interference :
  forall L (P : nat -> Prop) pc e1 e2 t a1 a2,
    env_LPequiv L P e1 e2 ->
    P, pc; e1 ⊢ t ⇓ a1 ->
    P, pc; e2 ⊢ t ⇓ a2 ->
    atom_Lequiv L a1 a2.
Proof.
  intros L P pc e1 e2 t a1 a2 He Heval1 Heval2.
  eapply non_interference_strong_observer in Heval2; eauto.
  eapply atom_LPequiv_Lequiv. eassumption.
Qed.
  
End NI.

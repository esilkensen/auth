Require Import Program.Tactics.
Require Import LambdaTwo.
Require Import LibTactics.

Section NI.

Lemma eval_kl_subset_n :
  forall n,
    forall k l,
      k + l < n ->
      (forall L P pc e t a,
         eval_kl (k, l) L P pc e t a ->
         eval_kl (S k, l) L P pc e t a) /\
      (forall L P pc e t a,
         eval_kl (k, S l) L P pc e t a ->
         eval_kl (k, l) L P pc e t a).
Proof.
  intro n. induction n; auto. split; introv Heval.
  - destruct t.
    + (* TBool *) 
      apply eval_kl_bool_inv in Heval.
      subst. apply eval_kl_bool.
    + (* TNat *)
      apply eval_kl_nat_inv in Heval.
      subst. apply eval_kl_nat.
    + (* TVar *)
      apply eval_kl_var_inv in Heval.
      destruct Heval as [v' [l' [H1 H2]]].
      subst. apply eval_kl_var. assumption.
    + (* TAbs *)
      apply eval_kl_abs_inv in Heval.
      subst. apply eval_kl_abs.
    + (* TApp *)
      apply eval_kl_app_inv in Heval.
      destruct Heval
        as [k' [e1' [t1' [l1 [a2 [a3 [H1 [H2 [H3 [H4 H5]]]]]]]]]].
      assert (H2': eval_kl (S k', l) L P pc e t1 (Atom (VClos e1' t1') l1))
        by (apply IHn in H2; try assumption; omega).
      assert (H3': eval_kl (S k', l) L P pc e t2 a2)
        by (apply IHn in H3; try assumption; omega).
      assert (H4': eval_kl (S k', l) L P l1 (a2 :: e1') t1' a3)
        by (apply IHn in H4; try assumption; omega).
      clear H2; clear H3; clear H4; subst.
      apply (eval_kl_app (S k') l L P pc e t1 t2 e1' t1' l1 a2 a3);
        assumption.
    + (* TDecl *)
      apply eval_kl_decl_inv in Heval; destruct Heval as [Heval | Heval].
      * (* E_Decl1 *)
        destruct Heval
          as [k' [e1' [t1' [l1 [a2 [v3 [H1 [H2 [H3 [H4 H5]]]]]]]]]].
        remember (Atom v3 Bottom2) as a3.
        assert (H2': eval_kl (S k', l) L P pc e t1 (Atom (VClos e1' t1') l1))
          by (apply IHn in H2; try assumption; omega).
        assert (H3': eval_kl (S k', l) L P pc e t2 a2)
          by (apply IHn in H3; try assumption; omega).
        assert (H4': eval_kl (S k', l) L P l1 (a2 :: e1') t1' a3)
          by (apply IHn in H4; try assumption; omega).
        clear H2; clear H3; clear H4; subst.
        apply (eval_kl_decl1 (S k') l L P pc e t1 t2 e1' t1' l1 a2 v3);
          assumption.
      * (* E_Decl2 *)
        destruct Heval
          as [k' [e1' [t1' [l1 [a2 [v3 [H1 [H2 [H3 [H4 [H5 H6]]]]]]]]]]].
        remember (Atom v3 Top2) as a3.
        assert (H2': eval_kl (S k', l) L P pc e t1 (Atom (VClos e1' t1') l1))
          by (apply IHn in H2; try assumption; omega).
        assert (H3': eval_kl (S k', l) L P pc e t2 a2)
          by (apply IHn in H3; try assumption; omega).
        assert (H4': eval_kl (S k', l) L P l1 (a2 :: e1') t1' a3)
          by (apply IHn in H4; try assumption; omega).
        assert (H5':
                  forall a2' e2' v3',
                    env_LPequiv L P (a2 :: e1') (a2' :: e2') ->
                    eval_kl (l, S k') L P pc (a2' :: e2') t1' (Atom v3' Top2) ->
                    value_LPequiv L P v3 v3')
          by (introv He H7; subst;
              assert (eval_kl (l, k') L P pc (a2' :: e2') t1' (Atom v3' Top2))
                by (apply IHn in H7; try omega; assumption);
              apply (H5 a2' e2' v3'); assumption).
        clear H2; clear H3; clear H4; clear H5; subst.
        apply (eval_kl_decl2 (S k') l L P pc e t1 t2 e1' t1' l1 a2 v3);
          assumption.
  - destruct t.
    + (* TBool *)
      apply eval_kl_bool_inv in Heval.
      subst. apply eval_kl_bool.
    + (* TNat *)
      apply eval_kl_nat_inv in Heval.
      subst. apply eval_kl_nat.
    + (* TVar *)
      apply eval_kl_var_inv in Heval.
      destruct Heval as [v' [l' [H1 H2]]].
      subst. apply eval_kl_var. assumption.
    + (* TAbs *)
      apply eval_kl_abs_inv in Heval.
      subst. apply eval_kl_abs.
    + (* TApp *) 
      apply eval_kl_app_inv in Heval.
      destruct Heval
        as [k' [e1' [t1' [l1 [a2 [a3 [H1 [H2 [H3 [H4 H5]]]]]]]]]].
      assert (H2': eval_kl (k', l) L P pc e t1 (Atom (VClos e1' t1') l1))
        by (apply IHn; try omega; assumption).
      assert (H3': eval_kl (k', l) L P pc e t2 a2)
        by (apply IHn; try omega; assumption).
      assert (H4': eval_kl (k', l) L P l1 (a2 :: e1') t1' a3)
        by (apply IHn; try omega; assumption).
      clear H2; clear H3; clear H4; subst.
      apply (eval_kl_app k' l L P pc e t1 t2 e1' t1' l1 a2 a3);
        assumption.
    + (* TDecl *)
      apply eval_kl_decl_inv in Heval; destruct Heval as [Heval | Heval].
      * (* E_Decl1 *)
        destruct Heval
          as [k' [e1' [t1' [l1 [a2 [v3 [H1 [H2 [H3 [H4 H5]]]]]]]]]].
        remember (Atom v3 Bottom2) as a3.
        assert (H2': eval_kl (k', l) L P pc e t1 (Atom (VClos e1' t1') l1))
          by (apply IHn; try omega; assumption).
        assert (H3': eval_kl (k', l) L P pc e t2 a2)
          by (apply IHn; try omega; assumption).
        assert (H4': eval_kl (k', l) L P l1 (a2 :: e1') t1' a3)
          by (apply IHn; try omega; assumption).
        clear H2; clear H3; clear H4; subst.
        apply (eval_kl_decl1 k' l L P pc e t1 t2 e1' t1' l1 a2 v3);
          assumption.
      * (* E_Decl2 *)
        destruct Heval
          as [k' [e1' [t1' [l1 [a2 [v3 [H1 [H2 [H3 [H4 [H5 H6]]]]]]]]]]].
        remember (Atom v3 Top2) as a3.
        assert (H2': eval_kl (k', l) L P pc e t1 (Atom (VClos e1' t1') l1))
          by (apply IHn; try omega; assumption).
        assert (H3': eval_kl (k', l) L P pc e t2 a2)
          by (apply IHn; try omega; assumption).
        assert (H4': eval_kl (k', l) L P l1 (a2 :: e1') t1' a3)
          by (apply IHn; try omega; assumption).
        assert (H5':
                  forall a2' e2' v3',
                    env_LPequiv L P (a2 :: e1') (a2' :: e2') ->
                    eval_kl (l, k') L P pc (a2' :: e2') t1' (Atom v3' Top2) ->
                    value_LPequiv L P v3 v3')
          by (introv He H7; subst;
              assert (eval_kl (S l, k') L P pc (a2' :: e2') t1' (Atom v3' Top2))
                by (apply IHn in H7; try assumption; omega);
              apply (H5 a2' e2' v3'); assumption).
        clear H2; clear H3; clear H4; clear H5; subst.
        apply (eval_kl_decl2 k' l L P pc e t1 t2 e1' t1' l1 a2 v3);
          assumption.
Qed.

Lemma eval_kl_subset :
  forall k l,
    (forall L P pc e t a,
       eval_kl (k, l) L P pc e t a ->
       eval_kl (S k, l) L P pc e t a) /\
    (forall L P pc e t a,
       eval_kl (k, S l) L P pc e t a ->
       eval_kl (k, l) L P pc e t a).
Proof.
  introv. apply (eval_kl_subset_n (S (k + l))). auto.
Qed.

Lemma non_interference_n :
  forall n k k' L P pc e e' t a a',
    k + k' < n ->
    env_LPequiv L P e e' ->
    (forall l, eval_kl (k, l) L P pc e t a) ->
    (forall l, eval_kl (k', l) L P pc e' t a') ->
    (forall v, P v v) ->
    atom_LPequiv L P a a'.
Proof.
  intro n. induction n; introv H He Heval1 Heval2 Prefl; auto.
  destruct t.
  - (* TBool *)
    apply eval_kl_bool_inv' in Heval1.
    apply eval_kl_bool_inv' in Heval2.
    subst. apply atom_LPequiv_refl. assumption.
  - (* TNat *)
    apply eval_kl_nat_inv' in Heval1.
    apply eval_kl_nat_inv' in Heval2.
    subst. apply atom_LPequiv_refl. assumption.
  - (* TVar *)
    apply eval_kl_var_inv' in Heval1.
    apply eval_kl_var_inv' in Heval2.
    destruct Heval1 as [v1' [l1' [He1 Ha1]]].
    destruct Heval2 as [v2' [l2' [He2 Ha2]]].
    assert (Ha: atom_LPequiv L P (Atom v1' l1') (Atom v2' l2'))
      by (eapply list_forall2_atIndex; eauto).
    assert (l2' = l1') by (apply atom_LPequiv_lab_inv in Ha; auto); subst.
    destruct pc; destruct l1'; simpl in *; auto.
    apply atom_LPequiv_raise; assumption.
  - (* TAbs *)
    apply eval_kl_abs_inv' in Heval1.
    apply eval_kl_abs_inv' in Heval2.
    subst. destruct L; destruct pc.
    + right. left. auto.
    + left. auto.
    + right. right. auto.
    + right. right. auto.
  - (* TApp *)
    apply eval_kl_app_inv' in Heval1.
    apply eval_kl_app_inv' in Heval2.
    destruct Heval1
      as [k1' [e11' [t11' [l11 [a21 [a31 [H1 [H2 [H3 [H4 H5]]]]]]]]]].
    destruct Heval2
      as [k1'' [e11'' [t11'' [l11' [a21' [a31' [H1' [H2' [H3' [H4' H5']]]]]]]]]].
    remember (Atom (VClos e11' t11') l11) as a1.
    remember (Atom (VClos e11'' t11'') l11') as a1'.
    assert (Ha1: atom_LPequiv L P a1 a1')
      by (apply IHn with (k := k1') (k' := k1'') (e := e) (e' := e')
                                    (a := a1) (a' := a1') in H2;
          try assumption; omega); subst.
    assert (l11' = l11)
      by (apply atom_LPequiv_lab_inv in Ha1; auto); subst.
    assert (t11'' = t11')
      by (destruct L; destruct Ha1; destruct H0; destruct_conjs; auto); subst.
    assert (He1: env_LPequiv L P e11' e11'')
      by (destruct L; destruct Ha1; destruct H0; destruct_conjs; auto).
    assert (Ha2: atom_LPequiv L P a21 a21')
      by (apply IHn with (k := k1') (k' := k1'') (e := e) (e' := e')
                                    (a := a21) (a' := a21') in H3;
          try assumption; omega).
    assert (He1': env_LPequiv L P (a21 :: e11') (a21' :: e11''))
      by (split; assumption).
    apply IHn with (k := k1') (k' := k1'') (e := (a21 :: e11'))
                              (e' := (a21' :: e11'')) (a := a31) (a' := a31')
      in H4; try assumption; omega.
  - (* TDecl *)
    admit.
Qed.

Theorem non_interference :
  forall L P pc e e' t a a',
    env_LPequiv L P e e' ->
    eval L P pc e t a ->
    eval L P pc e' t a' ->
    (forall v, P v v) ->
    atom_LPequiv L P a a'.
Proof.
  introv He Heval1 Heval2 Prefl.
  unfold eval in *.
  destruct Heval1 as [k Heval1].
  destruct Heval2 as [k' Heval2].
  eapply non_interference_n; eauto.
Qed.
  
End NI.

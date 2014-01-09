Require Import Program.Tactics.
Require Import LambdaTwo.
Require Import LibTactics.

Section NI.

Context
  (L : two)
  (P : value -> value -> Prop)
  (Prefl: forall v, P v v).
  
Lemma eval_kl_mon_n :
  forall n,
    forall k l,
      k + l < n ->
      (forall pc e t a,
         eval_kl (k, l) L P pc e t a ->
         eval_kl (S k, l) L P pc e t a) /\
      (forall pc e t a,
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
        as [k' [e1' [t1' [l1 [a2 [H1 [H2 [H3 H4]]]]]]]].
      assert (H2': eval_kl (S k', l) L P pc e t1 (Atom (VClos e1' t1') l1))
        by (apply IHn in H2; try assumption; omega).
      assert (H3': eval_kl (S k', l) L P pc e t2 a2)
        by (apply IHn in H3; try assumption; omega).
      assert (H4': eval_kl (S k', l) L P l1 (a2 :: e1') t1' a)
        by (apply IHn in H4; try assumption; omega).
      clear H2; clear H3; clear H4; subst.
      apply (eval_kl_app (S k') l L P pc e t1 t2 e1' t1' l1 a2 a);
        assumption.
    + (* TDecl *)
      apply eval_kl_decl_inv in Heval; destruct Heval as [Heval | Heval].
      * (* E_Decl1 *)
        destruct Heval as [k' [v [H1 [H2 H3]]]].
        assert (H2': eval_kl (S k', l) L P pc e t (Atom v Bottom2))
          by (apply IHn in H2; try assumption; omega).
        clear H2; subst.
        apply (eval_kl_decl1 (S k') l L P pc e t v);
          assumption.
      * (* E_Decl2 *)
        destruct Heval as [k' [v [H1 [H2 [H3 H4]]]]].
        assert (H2': eval_kl (S k', l) L P pc e t (Atom v Top2))
          by (apply IHn in H2; try assumption; omega).
        assert (H3': forall e' v',
                       env_LPequiv L P e e' ->
                       eval_kl (l, S k') L P pc e' t (Atom v' Top2) ->
                       value_LPequiv L P v v')
          by (introv He H5; subst;
              assert (eval_kl (l, k') L P pc e' t (Atom v' Top2))
                by (apply IHn in H5; try omega; assumption);
              apply (H3 e' v'); assumption).
        clear H2; clear H3; subst.
        apply (eval_kl_decl2 (S k') l L P pc e t v);
          assumption.
    + (* TIf *)
      apply eval_kl_if_inv in Heval; destruct Heval as [Heval | Heval].
      * (* E_IfTrue *)
        destruct Heval as [k' [l1 [H1 [H2 H3]]]].
        assert (H2': eval_kl (S k', l) L P pc e t1 (Atom (VNat 0) l1))
          by (apply IHn in H2; try assumption; omega).
        assert (H3': eval_kl (S k', l) L P (l1 ⊔ pc) e t2 a)
          by (apply IHn in H3; try assumption; omega).
        clear H2; clear H3; subst.
        apply (eval_kl_iftrue (S k') l L P pc e t1 t2 t3 l1 a);
          assumption.
      * (* E_IfFalse *)
        destruct Heval as [k' [n' [l1 [H1 [H2 H3]]]]].
        assert (H2': eval_kl (S k', l) L P pc e t1 (Atom (VNat (S n')) l1))
          by (apply IHn in H2; try assumption; omega).
        assert (H3': eval_kl (S k', l) L P (l1 ⊔ pc) e t3 a)
          by (apply IHn in H3; try assumption; omega).
        clear H2; clear H3; subst.
        apply (eval_kl_iffalse (S k') l L P pc e t1 t2 t3 l1 n' a);
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
      destruct Heval as [k' [e1' [t1' [l1 [a2 [H1 [H2 [H3 H4]]]]]]]].
      assert (H2': eval_kl (k', l) L P pc e t1 (Atom (VClos e1' t1') l1))
        by (apply IHn; try omega; assumption).
      assert (H3': eval_kl (k', l) L P pc e t2 a2)
        by (apply IHn; try omega; assumption).
      assert (H4': eval_kl (k', l) L P l1 (a2 :: e1') t1' a)
        by (apply IHn; try omega; assumption).
      clear H2; clear H3; clear H4; subst.
      apply (eval_kl_app k' l L P pc e t1 t2 e1' t1' l1 a2 a);
        assumption.
    + (* TDecl *)
      apply eval_kl_decl_inv in Heval; destruct Heval as [Heval | Heval].
      * (* E_Decl1 *)
        destruct Heval as [k' [v [H1 [H2 H3]]]].
        assert (H2': eval_kl (k', l) L P pc e t (Atom v Bottom2))
          by (apply IHn; try omega; assumption).
        clear H2; subst.
        apply (eval_kl_decl1 k' l L P pc e t v);
          assumption.
      * (* E_Decl2 *)
        destruct Heval as [k' [v [H1 [H2 [H3 H4]]]]].
        assert (H2': eval_kl (k', l) L P pc e t (Atom v Top2))
          by (apply IHn; try omega; assumption).
        assert (H3': forall e' v',
                       env_LPequiv L P e e' ->
                       eval_kl (l, k') L P pc e' t (Atom v' Top2) ->
                       value_LPequiv L P v v')
          by (introv He H5; subst;
              assert (eval_kl (S l, k') L P pc e' t (Atom v' Top2))
                by (apply IHn in H5; try assumption; omega);
              apply (H3 e' v'); assumption).
        clear H2; clear H3; subst.
        apply (eval_kl_decl2 k' l L P pc e t v);
          assumption.
    + (* TIf *)
      apply eval_kl_if_inv in Heval; destruct Heval as [Heval | Heval].
      * (* E_IfTrue *)
        destruct Heval as [k' [l1 [H1 [H2 H3]]]].
        assert (H2': eval_kl (k', l) L P pc e t1 (Atom (VNat 0) l1))
          by (apply IHn; try omega; assumption).
        assert (H3': eval_kl (k', l) L P (l1 ⊔ pc) e t2 a)
          by (apply IHn; try omega; assumption).
        clear H2; clear H3; subst.
        apply (eval_kl_iftrue k' l L P pc e t1 t2 t3 l1 a);
          assumption.
      * (* E_IfFalse *)
        destruct Heval as [k' [n' [l1 [H1 [H2 H3]]]]].
        assert (H2': eval_kl (k', l) L P pc e t1 (Atom (VNat (S n')) l1))
          by (apply IHn; try omega; assumption).
        assert (H3': eval_kl (k', l) L P (l1 ⊔ pc) e t3 a)
          by (apply IHn; try omega; assumption).
        clear H2; clear H3; subst.
        apply (eval_kl_iffalse k' l L P pc e t1 t2 t3 l1 n' a);
          assumption.
Qed.

Lemma eval_kl_mon :
  forall k l,
    (forall pc e t a,
       eval_kl (k, l) L P pc e t a ->
       eval_kl (S k, l) L P pc e t a) /\
    (forall pc e t a,
       eval_kl (k, S l) L P pc e t a ->
       eval_kl (k, l) L P pc e t a).
Proof.
  introv. apply (eval_kl_mon_n (S (k + l))). auto.
Qed.

Lemma eval_kl_mon_k_plus_n :
  forall n k l pc e t a,
    eval_kl (k, l) L P pc e t a ->
    eval_kl (n + k, l) L P pc e t a.
Proof.
  intro n. induction n; introv Heval; auto.
  apply IHn in Heval. apply eval_kl_mon in Heval. assumption.
Qed.

Lemma eval_kl_mon_k :
  forall k k' l pc e t a,
    k <= k' ->
    eval_kl (k, l) L P pc e t a ->
    eval_kl (k', l) L P pc e t a.
Proof.
  introv H Heval.
  apply (eval_kl_mon_k_plus_n (k' - k)) in Heval.
  assert (H': k' - k + k = k') by omega. rewrite H' in Heval.
  assumption.
Qed.

Lemma eval_kl_mon_l_minus_n :
  forall n k l pc e t a,
    eval_kl (k, n + l) L P pc e t a ->
    eval_kl (k, l) L P pc e t a.
Proof.
  intro n. induction n; introv Heval; auto.
  replace (S n + l) with (S (n + l)) in Heval.
  assert (H: eval_kl (k, n + l) L P pc e t a) 
    by (apply eval_kl_mon in Heval; assumption).
  apply IHn in H. assumption.
  reflexivity.
Qed.

Lemma eval_kl_mon_l :
  forall k l l' pc e t a,
    l >= l' ->
    eval_kl (k, l) L P pc e t a ->
    eval_kl (k, l') L P pc e t a.
Proof.
  introv H Heval.
  remember (l - l') as n.
  assert (H': l = n + l') by omega.
  rewrite H' in Heval.
  apply (eval_kl_mon_l_minus_n n k l') in Heval.
  assumption.
Qed.

Lemma non_interference_n :
  forall n k k' l pc e e' t a a',
    k + k' < n ->
    k < l ->
    k' < l ->
    env_LPequiv L P e e' ->
    eval_kl (k, l) L P pc e t a ->
    eval_kl (k', l) L P pc e' t a' ->
    atom_LPequiv L P a a'.
Proof.
  intro n. induction n; introv H Hk Hk' He Heval1 Heval2; auto.
  destruct t.
  - (* TBool *)
    apply eval_kl_bool_inv in Heval1.
    apply eval_kl_bool_inv in Heval2.
    subst. apply atom_LPequiv_refl. assumption.
  - (* TNat *)
    apply eval_kl_nat_inv in Heval1.
    apply eval_kl_nat_inv in Heval2.
    subst. apply atom_LPequiv_refl. assumption.
  - (* TVar *)
    apply eval_kl_var_inv in Heval1.
    apply eval_kl_var_inv in Heval2.
    destruct Heval1 as [v1' [l1' [He1 Ha1]]].
    destruct Heval2 as [v2' [l2' [He2 Ha2]]].
    assert (Ha: atom_LPequiv L P (Atom v1' l1') (Atom v2' l2'))
      by (eapply list_forall2_atIndex; eauto).
    assert (l2' = l1') by (apply atom_LPequiv_lab_inv in Ha; auto); subst.
    destruct pc; destruct l1'; simpl in *; auto.
    apply atom_LPequiv_raise; assumption.
  - (* TAbs *)
    apply eval_kl_abs_inv in Heval1.
    apply eval_kl_abs_inv in Heval2.
    subst. destruct L; destruct pc.
    + right. left. auto.
    + left. auto.
    + right. right. auto.
    + right. right. auto.
  - (* TApp *)
    apply eval_kl_app_inv in Heval1.
    apply eval_kl_app_inv in Heval2.
    destruct Heval1
      as [k1' [e11' [t11' [l11 [a21 [H1 [H2 [H3 H4]]]]]]]].
    destruct Heval2
      as [k1'' [e11'' [t11'' [l11' [a21' [H1' [H2' [H3' H4']]]]]]]].
    remember (Atom (VClos e11' t11') l11) as a1.
    remember (Atom (VClos e11'' t11'') l11') as a1'.
    assert (Ha1: atom_LPequiv L P a1 a1')
      by (apply (IHn k1' k1'' l pc e e' t1 a1 a1') in H2;
          try assumption; omega); subst.
    assert (l11' = l11)
      by (apply atom_LPequiv_lab_inv in Ha1; auto); subst.
    assert (t11'' = t11')
      by (destruct L; destruct Ha1; destruct H0; destruct_conjs; auto); subst.
    assert (He1: env_LPequiv L P e11' e11'')
      by (destruct L; destruct Ha1; destruct H0; destruct_conjs; auto).
    assert (Ha2: atom_LPequiv L P a21 a21')
      by (apply (IHn k1' k1'' l pc e e' t2 a21 a21') in H3;
          try assumption; omega).
    assert (He1': env_LPequiv L P (a21 :: e11') (a21' :: e11''))
      by (split; assumption).
    remember (a21 :: e11') as e2.
    remember (a21' :: e11'') as e2'.
    apply (IHn k1' k1'' l l11 e2 e2' t11' a a') in H4;
      try assumption; omega.
  - (* TDecl *)
    apply eval_kl_decl_inv in Heval1.
    apply eval_kl_decl_inv in Heval2.
    destruct Heval1 as [Heval1 | Heval1];
      destruct Heval2 as [Heval2 | Heval2];
      destruct Heval1 as [k1' [v11 Heval1]];
      destruct Heval2 as [k1'' [v11' Heval2]];
      destruct_conjs.
    + apply (IHn k1' k1'' l pc e e' t a a');
      try omega; subst; assumption.
    + remember (Atom v11 Bottom2) as a1;
      remember (Atom v11' Top2) as a1';
      assert (Ha1: atom_LPequiv L P a1 a1')
        by (apply (IHn k1' k1'' l pc e e' t a1 a1');
            try assumption; omega); subst.
      apply atom_LPequiv_lab_inv in Ha1.
      inversion Ha1.
    + remember (Atom v11 Top2) as a1;
      remember (Atom v11' Bottom2) as a1';
      assert (Ha1: atom_LPequiv L P a1 a1')
        by (apply (IHn k1' k1'' l pc e e' t a1 a1');
            try assumption; omega); subst.
      apply atom_LPequiv_lab_inv in Ha1.
      inversion Ha1.
    + remember (Atom v11 Top2) as a1.
      remember (Atom v11' Top2) as a1'.
      assert (Ha1: atom_LPequiv L P a1 a1')
        by (apply (IHn k1' k1'' l pc e e' t a1 a1') in H5;
            try assumption; omega).
      assert (H1': eval_kl (l, l) L P pc e' t a1')
        by (apply (eval_kl_mon_k k1'' l) in H1; try assumption; omega).
      assert (H1'': eval_kl (l, k1') L P pc e' t a1')
        by (apply (eval_kl_mon_l l l k1') in H1'; try assumption; omega).
      assert (value_LPequiv L P v11 v11')
        by (subst; apply (H6 e' v11') in H1''; assumption); subst.
      destruct L.
      * right; left; auto. 
      * right; right; auto.
  - (* TIf *)
    apply eval_kl_if_inv in Heval1.
    apply eval_kl_if_inv in Heval2.
    destruct Heval1 as [Heval1 | Heval1];
      destruct Heval2 as [Heval2 | Heval2];
      destruct Heval1 as [k1 Heval1];
      destruct Heval2 as [k1' Heval2].
    + destruct Heval1 as [l1 [H1 [H2 H3]]].
      destruct Heval2 as [l1' [H1' [H2' H3']]].
      remember (Atom (VNat 0) l1) as a1.
      remember (Atom (VNat 0) l1') as a1'.
      assert (Ha1: atom_LPequiv L P a1 a1')
        by (apply (IHn k1 k1' l pc e e' t1 a1 a1');
            try omega; assumption); subst.
      assert (l1' = l1)
        by (apply atom_LPequiv_lab_inv in Ha1; auto); subst.
      apply (IHn k1 k1' l (l1 ⊔ pc) e e' t2 a a');
        try omega; assumption.
    + destruct Heval1 as [l1 [H1 [H2 H3]]].
      destruct Heval2 as [n1' [l1' [H1' [H2' H3']]]].
      remember (Atom (VNat 0) l1) as a1.
      remember (Atom (VNat (S n1')) l1') as a1'.
      assert (Ha1: atom_LPequiv L P a1 a1')
        by (apply (IHn k1 k1' l pc e e' t1 a1 a1');
            try omega; assumption); subst.
      assert (l1' = l1)
        by (apply atom_LPequiv_lab_inv in Ha1; auto); subst.
      inversion Ha1.
      * destruct_conjs; subst. simpl in *.
        admit.
      * destruct H0; destruct_conjs; inversion H4; inversion H5.
    + destruct Heval1 as [n1 [l1 [H1 [H2 H3]]]].
      destruct Heval2 as [l1' [H1' [H2' H3']]].
      remember (Atom (VNat (S n1)) l1) as a1.
      remember (Atom (VNat 0) l1') as a1'.
      assert (Ha1: atom_LPequiv L P a1 a1')
        by (apply (IHn k1 k1' l pc e e' t1 a1 a1');
            try omega; assumption); subst.
      assert (l1' = l1)
        by (apply atom_LPequiv_lab_inv in Ha1; auto); subst.
      inversion Ha1.
      * destruct_conjs; subst. simpl in *.
        admit.
      * destruct H0; destruct_conjs; inversion H4; inversion H5.
    + destruct Heval1 as [n1 [l1 [H1 [H2 H3]]]].
      destruct Heval2 as [n1' [l1' [H1' [H2' H3']]]].
      remember (Atom (VNat (S n1)) l1) as a1.
      remember (Atom (VNat (S n1')) l1') as a1'.
      assert (Ha1: atom_LPequiv L P a1 a1')
        by (apply (IHn k1 k1' l pc e e' t1 a1 a1');
            try omega; assumption); subst.
      assert (l1' = l1)
        by (apply atom_LPequiv_lab_inv in Ha1; auto); subst.
      apply (IHn k1 k1' l (l1 ⊔ pc) e e' t3 a a');
        try omega; assumption.
Qed.

Theorem non_interference :
  forall pc e e' t a a',
    env_LPequiv L P e e' ->
    eval L P pc e t a ->
    eval L P pc e' t a' ->
    atom_LPequiv L P a a'.
Proof.
  introv He Heval1 Heval2.
  unfold eval in *.
  destruct Heval1 as [k Heval1].
  destruct Heval2 as [k' Heval2].
  assert (H1: eval_kl (k, (S (k + k'))) L P pc e t a) by apply Heval1.
  assert (H2: eval_kl (k', (S (k + k'))) L P pc e' t a') by apply Heval2.
  remember (S (k + k')) as n.
  apply (non_interference_n n k k' n pc e e' t a a');
    try omega; assumption.
Qed.

End NI.

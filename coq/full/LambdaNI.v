Require Import Classical.
Require Import Program.Tactics.
Require Import Lambda.
Require Import LibTactics.

Section NI.

Context
  (L : Type)
  (M : LabelAlgebra unit L)
  (l : L)
  (P : value L -> value L -> Prop)
  (Prefl : forall v, P v v)
  (Psym : forall v1 v2, P v1 v2 -> P v2 v1)
  (Ltotal : forall l l', l ⊑ l' \/ l' ⊑ l).

Lemma eval_km_mon_n :
  forall n,
    forall k m,
      k + m < n ->
      (forall pc e t a,
         eval_km (k, m) l P pc e t a ->
         eval_km (S k, m) l P pc e t a) /\
      (forall pc e t a,
         eval_km (k, S m) l P pc e t a ->
         eval_km (k, m) l P pc e t a).
Proof.
  intro n. induction n; auto. split; introv Heval.
  - destruct t.
    + (* TBool *) 
      apply eval_km_bool_inv in Heval.
      subst. apply eval_km_bool.
    + (* TNat *)
      apply eval_km_nat_inv in Heval.
      subst. apply eval_km_nat.
    + (* TVar *)
      apply eval_km_var_inv in Heval.
      destruct Heval as [v' [l' [H1 H2]]].
      subst. apply eval_km_var. assumption.
    + (* TAbs *)
      apply eval_km_abs_inv in Heval.
      subst. apply eval_km_abs.
    + (* TApp *)
      apply eval_km_app_inv in Heval.
      destruct Heval
        as [k' [e1' [t1' [l1 [a2 [H1 [H2 [H3 H4]]]]]]]].
      assert (H2': eval_km (S k', m) l P pc e t1 (Atom (VClos e1' t1') l1))
        by (apply IHn in H2; try assumption; omega).
      assert (H3': eval_km (S k', m) l P pc e t2 a2)
        by (apply IHn in H3; try assumption; omega).
      assert (H4': eval_km (S k', m) l P l1 (a2 :: e1') t1' a)
        by (apply IHn in H4; try assumption; omega).
      clear H2; clear H3; clear H4; subst.
      apply (eval_km_app (S k') m l P pc e t1 t2 e1' t1' l1 a2 a);
        assumption.
    + (* TRelabel *)
      apply eval_km_relabel_inv in Heval; destruct Heval as [Heval | Heval].
      * (* E_Relabel1 *)
        destruct Heval as [k' [v [l1 [H1 [H2 [H3 H4]]]]]].
        assert (H2': eval_km (S k', m) l P pc e t (Atom v l1))
          by (apply IHn in H2; try assumption; omega).
        clear H2; subst.
        apply (eval_km_relabel_up (S k') m l P pc e t l0 v l1);
          assumption.
      * (* E_Relabel2 *)
        destruct Heval as [k' [v [l1 [H1 [H2 [H3 [H4 H5]]]]]]].
        assert (H2': eval_km (S k', m) l P pc e t (Atom v l1))
          by (apply IHn in H2; try assumption; omega).
        assert (H4': forall pc' e' v' l1',
                       lab_Lequiv L M l pc pc' ->
                       env_LPequiv L M l P e e' ->
                       lab_Lequiv L M l l1 l1' ->
                       eval_km (m, S k') l P pc' e' t (Atom v' l1') ->
                       value_LPequiv L M l P v v')
          by (introv Hpc He Hl1 H6; subst;
              assert (eval_km (m, k') l P pc' e' t (Atom v' l1'))
                by (apply IHn in H6; try omega; assumption);
              apply (H4 pc' e' v' l1'); assumption).
        clear H2; clear H4; subst.
        apply (eval_km_relabel_down (S k') m l P pc e t l0 v l1);
          assumption.
  - destruct t.
    + (* TBool *)
      apply eval_km_bool_inv in Heval.
      subst. apply eval_km_bool.
    + (* TNat *)
      apply eval_km_nat_inv in Heval.
      subst. apply eval_km_nat.
    + (* TVar *)
      apply eval_km_var_inv in Heval.
      destruct Heval as [v' [l' [H1 H2]]].
      subst. apply eval_km_var. assumption.
    + (* TAbs *)
      apply eval_km_abs_inv in Heval.
      subst. apply eval_km_abs.
    + (* TApp *) 
      apply eval_km_app_inv in Heval.
      destruct Heval as [k' [e1' [t1' [l1 [a2 [H1 [H2 [H3 H4]]]]]]]].
      assert (H2': eval_km (k', m) l P pc e t1 (Atom (VClos e1' t1') l1))
        by (apply IHn; try omega; assumption).
      assert (H3': eval_km (k', m) l P pc e t2 a2)
        by (apply IHn; try omega; assumption).
      assert (H4': eval_km (k', m) l P l1 (a2 :: e1') t1' a)
        by (apply IHn; try omega; assumption).
      clear H2; clear H3; clear H4; subst.
      apply (eval_km_app k' m l P pc e t1 t2 e1' t1' l1 a2 a);
        assumption.
    + (* TRelabel *)
      apply eval_km_relabel_inv in Heval; destruct Heval as [Heval | Heval].
      * (* E_Relabel1 *)
        destruct Heval as [k' [v [l1 [H1 [H2 [H3 H4]]]]]].
        assert (H2': eval_km (k', m) l P pc e t (Atom v l1))
          by (apply IHn; try omega; assumption).
        clear H2; subst.
        apply (eval_km_relabel_up k' m l P pc e t l0 v l1);
          assumption.
      * (* E_Relabel2 *)
        destruct Heval as [k' [v [l1 [H1 [H2 [H3 [H4 H5]]]]]]].
        assert (H2': eval_km (k', m) l P pc e t (Atom v l1))
          by (apply IHn; try omega; assumption).
        assert (H4': forall pc' e' v' l1',
                       lab_Lequiv L M l pc pc' ->
                       env_LPequiv L M l P e e' ->
                       lab_Lequiv L M l l1 l1' ->
                       eval_km (m, k') l P pc' e' t (Atom v' l1') ->
                       value_LPequiv L M l P v v')
          by (introv Hpc He Hl1 H6; subst;
              assert (eval_km (S m, k') l P pc' e' t (Atom v' l1'))
                by (apply IHn in H6; try assumption; omega);
              apply (H4 pc' e' v' l1'); assumption).
        clear H2; clear H4; subst.
        apply (eval_km_relabel_down k' m l P pc e t l0 v l1);
          assumption.
Qed.

Lemma eval_km_mon :
  forall k m,
    (forall pc e t a,
       eval_km (k, m) l P pc e t a ->
       eval_km (S k, m) l P pc e t a) /\
    (forall pc e t a,
       eval_km (k, S m) l P pc e t a ->
       eval_km (k, m) l P pc e t a).
Proof.
  introv. apply (eval_km_mon_n (S (k + m))). auto.
Qed.

Lemma eval_km_mon_k_plus_n :
  forall n k m pc e t a,
    eval_km (k, m) l P pc e t a ->
    eval_km (n + k, m) l P pc e t a.
Proof.
  intro n. induction n; introv Heval; auto.
  apply IHn in Heval. apply eval_km_mon in Heval. assumption.
Qed.

Lemma eval_km_mon_k :
  forall k k' m pc e t a,
    k <= k' ->
    eval_km (k, m) l P pc e t a ->
    eval_km (k', m) l P pc e t a.
Proof.
  introv H Heval.
  apply (eval_km_mon_k_plus_n (k' - k)) in Heval.
  assert (H': k' - k + k = k') by omega. rewrite H' in Heval.
  assumption.
Qed.

Lemma eval_km_mon_m_minus_n :
  forall n k m pc e t a,
    eval_km (k, n + m) l P pc e t a ->
    eval_km (k, m) l P pc e t a.
Proof.
  intro n. induction n; introv Heval; auto.
  replace (S n + m) with (S (n + m)) in Heval.
  assert (H: eval_km (k, n + m) l P pc e t a) 
    by (apply eval_km_mon in Heval; assumption).
  apply IHn in H. assumption.
  reflexivity.
Qed.

Lemma eval_km_mon_m :
  forall k m m' pc e t a,
    m >= m' ->
    eval_km (k, m) l P pc e t a ->
    eval_km (k, m') l P pc e t a.
Proof.
  introv H Heval.
  remember (m - m') as n.
  assert (H': m = n + m') by omega.
  rewrite H' in Heval.
  apply (eval_km_mon_m_minus_n n k m') in Heval.
  assumption.
Qed.

Lemma non_interference_n :
  forall n k k' m pc pc' e e' t a a',
    k + k' < n ->
    k < m ->
    k' < m ->
    lab_Lequiv L M l pc pc' ->
    env_LPequiv L M l P e e' ->
    eval_km (k, m) l P pc e t a ->
    eval_km (k', m) l P pc' e' t a' ->
    atom_LPequiv L M l P a a'.
Proof.
  intro n. induction n; introv H Hk Hk' Hpc He Heval1 Heval2; auto.
  destruct t.
  - (* TBool *)
    apply eval_km_bool_inv in Heval1.
    apply eval_km_bool_inv in Heval2. subst.
    split; auto.
  - (* TNat *)
    apply eval_km_nat_inv in Heval1.
    apply eval_km_nat_inv in Heval2. subst.
    split; auto.
  - (* TVar *)
    apply eval_km_var_inv in Heval1.
    apply eval_km_var_inv in Heval2.
    destruct Heval1 as [v1' [l1' [He1 Ha1]]].
    destruct Heval2 as [v2' [l2' [He2 Ha2]]].
    assert (Ha: atom_LPequiv L M l P (Atom v1' l1') (Atom v2' l2'))
      by (eapply list_forall2_atIndex; eauto). subst.
    apply atom_LPequiv_lab_Lequiv_raise; auto.
  - (* TAbs *)
    apply eval_km_abs_inv in Heval1.
    apply eval_km_abs_inv in Heval2. subst.
    assert (H1: pc ⊑ l \/ ~ pc ⊑ l) by apply classic.
    split; auto.
  - (* TApp *)
    apply eval_km_app_inv in Heval1.
    apply eval_km_app_inv in Heval2.
    destruct Heval1
      as [k1' [e11' [t11' [l11 [a21 [H1 [H2 [H3 H4]]]]]]]].
    destruct Heval2
      as [k1'' [e11'' [t11'' [l11' [a21' [H1' [H2' [H3' H4']]]]]]]].
    remember (Atom (VClos e11' t11') l11) as a1.
    remember (Atom (VClos e11'' t11'') l11') as a1'.
    assert (Ha1: atom_LPequiv L M l P a1 a1')
      by (apply (IHn k1' k1'' m pc pc' e e' t1 a1 a1') in H2;
          try assumption; omega); subst.
    assert (Ha2: atom_LPequiv L M l P a21 a21')
      by (apply (IHn k1' k1'' m pc pc' e e' t2 a21 a21') in H3;
          try assumption; omega).
    assert (Hinv: env_LPequiv L M l P e11' e11'' /\ t11'' = t11' /\
                  lab_Lequiv L M l l11 l11')
      by (inversion Ha1 as [Ha1a Ha1b];
          fold (atom_LPequiv L M l P) in *;
            assert (Hl11: l11 ⊑ l \/ l ⊑ l11) by auto;
          assert (Hl11': l11' ⊑ l \/ l ⊑ l11') by auto;
          destruct Hl11 as [Hl11 | Hl11];
          destruct Hl11' as [Hl11' | Hl11'];
          try (assert (Hl: l11 ⊑ l \/ l11' ⊑ l) by auto;
               apply Ha1a in Hl; destruct Hl as [[Hla Hlb] Hlc]; auto);
          try (assert (Hl': (l11 ⊑ l \/ l11' ⊑ l) \/ ~ (l11 ⊑ l \/ l11' ⊑ l))
                by apply classic;
               destruct Hl' as [Hl' | Hl'];
               try (apply Ha1a in Hl'; destruct Hl' as [[Hla Hlb] Hlc]; auto);
               try (assert (Hl: ~ (l11 ⊑ l \/ l11' ⊑ l) /\ l ⊑ l11 /\ l ⊑ l11')
                     by auto;
                    apply Ha1b in Hl; destruct Hl; splits; auto; right; auto))).
    destruct Hinv as [He11 [Ht11 Hl11]]. subst.
    apply (IHn k1' k1'' m l11 l11' (a21 :: e11') (a21' :: e11'') t11' a a');
      try omega; try split; assumption.
  - (* TRelabel *)
    apply eval_km_relabel_inv in Heval1.
    apply eval_km_relabel_inv in Heval2.
    destruct Heval1 as [Heval1 | Heval1];
      destruct Heval2 as [Heval2 | Heval2];
      destruct Heval1 as [k1' [v11 [l11 Heval1]]];
      destruct Heval2 as [k1'' [v11' [l11' Heval2]]];
      destruct_conjs.
    + remember (Atom v11 l11) as a1.
      remember (Atom v11' l11') as a1'.
      assert (Ha1: atom_LPequiv L M l P a1 a1')
        by (apply (IHn k1' k1'' m pc pc' e e' t a1 a1');
            try omega; assumption); subst.
      apply atom_LPequiv_lab_Lequiv_raise with (l1 := l11) (l2 := l11');
        try apply lab_Lequiv_refl; auto.
    + remember (Atom v11 l11) as a1.
      remember (Atom v11' l11') as a1'.
      assert (Ha1: atom_LPequiv L M l P a1 a1')
        by (apply (IHn k1' k1'' m pc pc' e e' t a1 a1');
            try omega; assumption); subst.
      assert (Hl11: lab_Lequiv L M l l11 l11')
        by (eapply atom_LPequiv_lab_inv; eauto).
      split; intro Hl; destruct Ha1 as [Ha11 Ha12];
      fold (value_LPequiv L M l P v11 v11') in *.
      * destruct Hl11 as [Hl11 | Hl11].
          destruct Hl11 as [Hl11 Hl11'].
            apply Ha11 in Hl11. destruct Hl11 as [Hl11a Hl11b].
            split. assumption.
            left. split. assumption. split; auto.
          destruct Hl11 as [Hl11 [Hl11a Hl11b]].
            assert (~ l11 ⊑ l) by auto.
            destruct Hl as [Hl | Hl].
              assert (l11 ⊑ l) by (transitivity (l11 ⊔ l0); auto);
                contradiction.
              assert (l11 ⊑ l) by (transitivity l0; auto).
                contradiction.
      * destruct v11; destruct v11'; try reflexivity;
        (destruct Hl11 as [Hl11 | Hl11]; [
           destruct Hl11 as [Hl11 Hl11'];
           apply Ha11 in Hl11; destruct Hl11 as [Hl11a Hl11b];
           inversion Hl11a; auto |
           destruct Hl11 as [Hl11 [Hl11a Hl11b]];
             destruct Hl as [Hla [Hlb Hlc]];
             assert (~ l11 ⊑ l) by auto;
             assert (Htmp: l11 ⊑ l \/ l ⊑ l11) by auto;
             destruct Htmp as [Htmp | Htmp]; try contradiction;
             assert (Htmp': ~ (l11 ⊑ l \/ l11' ⊑ l) /\ l ⊑ l11 /\ l ⊑ l11')
               by auto; apply Ha12 in Htmp'; assumption
         ]).
    + remember (Atom v11 l11) as a1.
      remember (Atom v11' l11') as a1'.
      assert (Ha1: atom_LPequiv L M l P a1 a1')
        by (apply (IHn k1' k1'' m pc pc' e e' t a1 a1');
            try omega; assumption); subst.
      assert (Hl11: lab_Lequiv L M l l11 l11')
        by (eapply atom_LPequiv_lab_inv; eauto).
      split; intro Hl; destruct Ha1 as [Ha11 Ha12];
      fold (value_LPequiv L M l P v11 v11') in *.
      * destruct Hl11 as [Hl11 | Hl11].
          destruct Hl11 as [Hl11 Hl11'].
            apply Ha11 in Hl11. destruct Hl11 as [Hl11a Hl11b].
            split. assumption.
            left. split. assumption. split; auto.
          destruct Hl11 as [Hl11 [Hl11a Hl11b]].
            assert (~ l11 ⊑ l) by auto.
            destruct Hl as [Hl | Hl].
              assert (l11' ⊑ l) by (transitivity l0; auto).
                assert (Htmp: l11 ⊑ l \/ l11' ⊑ l) by auto.
                apply Ha11 in Htmp. destruct Htmp as [Htmp1 Htmp2].
                split. assumption. left. split. left. assumption. split; auto.
              assert (Htmp: l11 ⊑ l \/ l11' ⊑ l)
                  by (right; transitivity (l11' ⊔ l0); auto).
              apply Ha11 in Htmp. destruct Htmp as [Htmp1 Htmp2].
              split. assumption. left. split. right. assumption. split; auto.
      * destruct v11; destruct v11'; try reflexivity;
        (destruct Hl11 as [Hl11 | Hl11]; [
           destruct Hl11 as [Hl11 Hl11'];
           apply Ha11 in Hl11; destruct Hl11 as [Hl11a Hl11b];
           inversion Hl11a; auto |
           destruct Hl11 as [Hl11 [Hl11a Hl11b]];
             destruct Hl as [Hla [Hlb Hlc]];
             assert (~ l11 ⊑ l) by auto;
             assert (Htmp: l11 ⊑ l \/ l ⊑ l11) by auto;
             destruct Htmp as [Htmp | Htmp]; try contradiction;
             assert (Htmp': ~ (l11 ⊑ l \/ l11' ⊑ l) /\ l ⊑ l11 /\ l ⊑ l11')
               by auto; apply Ha12 in Htmp'; assumption
         ]).
    + remember (Atom v11 l11) as a1.
      remember (Atom v11' l11') as a1'.
      assert (Ha1: atom_LPequiv L M l P a1 a1')
        by (apply (IHn k1' k1'' m pc pc' e e' t a1 a1');
            try omega; assumption).
      assert (Hl11: lab_Lequiv L M l l11 l11')
        by (subst; eapply atom_LPequiv_lab_inv; eauto).
      assert (H1': eval_km (m, m) l P pc' e' t a1')
        by (apply (eval_km_mon_k k1'' m); try omega; assumption).
      assert (H1'': eval_km (m, k1') l P pc' e' t a1')
        by (apply (eval_km_mon_m m m k1'); try omega; assumption).
      assert (Hv: value_LPequiv L M l P v11 v11')
        by (subst; apply (H8 pc' e' v11' l11'); assumption); subst.
      split; intro Hl; fold (value_LPequiv L M l P v11 v11').
      * split; try apply lab_Lequiv_refl; assumption.
      * destruct v11; destruct v11'; try reflexivity.
        inversion Hv. auto. assumption.
Qed.

Theorem non_interference :
  forall pc pc' e e' t a a',
    env_LPequiv L M l P e e' ->
    pc =L pc' ->
    eval l P pc e t a ->
    eval l P pc' e' t a' ->
    atom_LPequiv L M l P a a'.
Proof.
  introv He Hpc Heval1 Heval2.
  unfold eval in *.
  destruct Heval1 as [k Heval1].
  destruct Heval2 as [k' Heval2].
  assert (H1: eval_km (k, (S (k + k'))) l P pc e t a) by apply Heval1.
  assert (H2: eval_km (k', (S (k + k'))) l P pc' e' t a') by apply Heval2.
  remember (S (k + k')) as n.
  apply (non_interference_n n k k' n pc pc' e e' t a a');
    try omega; try apply labEquiv_lab_Lequiv; auto.
Qed.

End NI.

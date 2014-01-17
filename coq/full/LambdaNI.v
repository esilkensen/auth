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
  (Prefl: forall v, P v v).

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
        assert (H4': forall e' v',
                       env_LPequiv L M l P e e' ->
                       eval_km (m, S k') l P pc e' t (Atom v' l1) ->
                       value_LPequiv L M l P v v')
          by (introv He H6; subst;
              assert (eval_km (m, k') l P pc e' t (Atom v' l1))
                by (apply IHn in H6; try omega; assumption);
              apply (H4 e' v'); assumption).
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
        assert (H4': forall e' v',
                       env_LPequiv L M l P e e' ->
                       eval_km (m, k') l P pc e' t (Atom v' l1) ->
                       value_LPequiv L M l P v v')
          by (introv He H6; subst;
              assert (eval_km (S m, k') l P pc e' t (Atom v' l1))
                by (apply IHn in H6; try assumption; omega);
              apply (H4 e' v'); assumption).
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
  forall n k k' m pc e e' t a a',
    k + k' < n ->
    k < m ->
    k' < m ->
    env_LPequiv L M l P e e' ->
    eval_km (k, m) l P pc e t a ->
    eval_km (k', m) l P pc e' t a' ->
    atom_LPequiv L M l P a a'.
Proof.
  intro n. induction n; introv H Hk Hk' He Heval1 Heval2; auto.
  destruct t.
  - (* TBool *)
    apply eval_km_bool_inv in Heval1.
    apply eval_km_bool_inv in Heval2. subst.
    apply atom_LPequiv_refl. assumption.
  - (* TNat *)
    apply eval_km_nat_inv in Heval1.
    apply eval_km_nat_inv in Heval2. subst.
    apply atom_LPequiv_refl. assumption.
  - (* TVar *)
    apply eval_km_var_inv in Heval1.
    apply eval_km_var_inv in Heval2.
    destruct Heval1 as [v1' [l1' [He1 Ha1]]].
    destruct Heval2 as [v2' [l2' [He2 Ha2]]].
    assert (Ha: atom_LPequiv L M l P (Atom v1' l1') (Atom v2' l2'))
      by (eapply list_forall2_atIndex; eauto). subst.
    split; intro H1; destruct Ha as [Ha1 Ha2];
    fold (value_LPequiv L M l P v1' v2') in *.
    + assert (H1': l1' ⊑ l \/ l2' ⊑ l)
        by (destruct H1; [
              left; transitivity (l1' ⊔ pc); auto |
              right; transitivity (l2' ⊔ pc); auto
            ]).
      apply Ha1 in H1'. destruct H1' as [H1'a H1'b].
      split; try apply labEquiv_join; auto. 
    + (* TODO: what is the correct definition of atom_LPequiv? *)
      admit.
  - (* TAbs *)
    apply eval_km_abs_inv in Heval1.
    apply eval_km_abs_inv in Heval2. subst.
    assert (H1: pc ⊑ l \/ ~ pc ⊑ l) by apply classic.
    destruct H1; split; auto.
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
      by (apply (IHn k1' k1'' m pc e e' t1 a1 a1') in H2;
          try assumption; omega); subst.
    admit.
  - (* TRelabel *)
    apply eval_km_relabel_inv in Heval1.
    apply eval_km_relabel_inv in Heval2.
    admit.
Qed.

Theorem non_interference :
  forall pc e e' t a a',
    env_LPequiv L M l P e e' ->
    eval l P pc e t a ->
    eval l P pc e' t a' ->
    atom_LPequiv L M l P a a'.
Proof.
  introv He Heval1 Heval2.
  unfold eval in *.
  destruct Heval1 as [k Heval1].
  destruct Heval2 as [k' Heval2].
  assert (H1: eval_km (k, (S (k + k'))) l P pc e t a) by apply Heval1.
  assert (H2: eval_km (k', (S (k + k'))) l P pc e' t a') by apply Heval2.
  remember (S (k + k')) as n.
  apply (non_interference_n n k k' n pc e e' t a a');
    try omega; assumption.
Qed.

End NI.

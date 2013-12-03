Require Import Program.Tactics.
Require Import LambdaTwo.
Require Import LibTactics.

Section NI.

Lemma non_interference_n :
  forall n,
    forall k k' L P pc e e' t a a',
      k + k' < n ->
      env_LPequiv L P e e' ->
      eval_k k L P pc e t a ->
      eval_k k' L P pc e' t a' ->
      (forall v, P v v) ->
      atom_LPequiv L P a a'.
Proof.
  intro n. induction n; introv Hn He Heval1 Heval2 Prefl.
  - inversion Hn.
  - destruct t.
    + (* TBool *)
      destruct k; destruct k'; 
      (inversion Heval1; inversion Heval2;
       destruct L; destruct pc; [
         right; left; auto |
         left; auto |
         right; right; auto |
         right; right; auto
      ]).
    + (* TNat *)
      destruct k; destruct k'; 
      (inversion Heval1; inversion Heval2;
       destruct L; destruct pc; [
         right; left; auto |
         left; auto |
         right; right; auto |
         right; right; auto
      ]).
    + (* TVar *)
      destruct k; destruct k';
      inversion Heval1 as [v1 Ha1]; destruct Ha1 as [l1 [Ha1 Ha]];
      inversion Heval2 as [v2 Ha2]; destruct Ha2 as [l2 [Ha2 Ha']]; subst;
      assert (Ha1a2: atom_LPequiv L P (Atom v1 l1) (Atom v2 l2)) by
          (eapply list_forall2_atIndex; eauto);
      assert (l2 = l1) by (apply atom_LPequiv_lab_inv in Ha1a2; auto); subst;
      destruct pc; destruct l1; simpl; auto;
      apply atom_LPequiv_raise; auto.
    + (* TAbs *)
      destruct k; destruct k'; 
      (inversion Heval1; inversion Heval2;
       destruct L; destruct pc; [
         right; left; auto |
         left; auto |
         right; right; auto |
         right; right; auto
      ]).
    + (* TApp *)
      destruct k; destruct k';
      inversion Heval1; inversion Heval2.
      rename x into e1; rename x0 into e1'.
      destruct H as
          [t1' [l1 [a2 [a3 [Heval1a [Heval1b [Heval1c Ha1]]]]]]].
      destruct H0 as
          [t1'' [l1' [a2' [a3' [Heval2a [Heval2b [Heval2c Ha2]]]]]]].
      subst.
      remember (Atom (VClos e1 t1') l1) as a1;
      remember (Atom (VClos e1' t1'') l1') as a1'.
      assert (atom_LPequiv L P a1 a1') by (eapply IHn; eauto; omega); subst.
      assert (l1' = l1) by (apply atom_LPequiv_lab_inv in H; auto); subst.
      assert (env_LPequiv L P e1 e1' /\ t1'' = t1') by
          (split; destruct H; destruct H; destruct_conjs; subst; auto);
        destruct_conjs; subst.
      assert (atom_LPequiv L P a2 a2') by
          (apply IHn with
           (k := k) (k' := k') (pc := pc) (e := e) (e' := e') (t := t2);
           try omega; auto).
      assert (env_LPequiv L P (a2 :: e1) (a2' :: e1')) by (split; auto).
      eapply IHn; eauto; omega.
    + (* TDecl *)
      destruct k; destruct k';
      inversion Heval1; inversion Heval2.
      rename x into e1; rename x0 into e1'.
      destruct H as
          [t1' [l1 [a2 [v3 [l3 [Heval1a [Heval1b [Heval1c Ha1]]]]]]]].
      destruct H0 as
          [t1'' [l1' [a2' [v3' [l3' [Heval2a [Heval2b [Heval2c Ha2]]]]]]]].
      subst.
      remember (Atom (VClos e1 t1') l1) as a1;
      remember (Atom (VClos e1' t1'') l1') as a1'.
      assert (atom_LPequiv L P a1 a1') by (eapply IHn; eauto; omega); subst.
      assert (l1' = l1) by (apply atom_LPequiv_lab_inv in H; auto); subst.
      assert (env_LPequiv L P e1 e1' /\ t1'' = t1') by
          (split; destruct H; destruct H; destruct_conjs; subst; auto);
        destruct_conjs; subst.
      assert (atom_LPequiv L P a2 a2') by
          (apply IHn with
           (k := k) (k' := k') (pc := pc) (e := e) (e' := e') (t := t2);
           try omega; auto).
      assert (env_LPequiv L P (a2 :: e1) (a2' :: e1')) by (split; auto).
      assert (atom_LPequiv L P (Atom v3 l3) (Atom v3' l3')) by
          (eapply IHn; eauto; omega).
      assert (l3' = l3) by (apply atom_LPequiv_lab_inv in H3; auto); subst.
      destruct l3; destruct_conjs; subst; auto.
      assert (value_LPequiv L P v3 v3').
      eapply H6; eauto.
      Admitted.

Theorem non_interference :
  forall k k' L P pc e e' t a a',
    env_LPequiv L P e e' ->
    eval_k k L P pc e t a ->
    eval_k k' L P pc e' t a' ->
    (forall v, P v v) ->
    atom_LPequiv L P a a'.
Proof.
  introv He Heval1 Heval2 Prefl.
  eapply non_interference_n; eauto.
Qed.
  
End NI.

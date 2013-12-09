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
      destruct Heval as [k' [e1' [t1' [l1 [a2 [a3 [H1 [H2 [H3 [H4 H5]]]]]]]]]].
      assert (H2': eval_kl (S k', l) L P pc e t1 (Atom (VClos e1' t1') l1)) by
          (apply IHn in H2; try assumption; omega).
      assert (H3': eval_kl (S k', l) L P pc e t2 a2) by
          (apply IHn in H3; try assumption; omega).
      assert (H4': eval_kl (S k', l) L P l1 (a2 :: e1') t1' a3) by
          (apply IHn in H4; try assumption; omega).
      clear H2; clear H3; clear H4; subst.
      apply (eval_kl_app (S k') l L P pc e t1 t2 e1' t1' l1 a2 a3); assumption.
    + (* TDecl *)
      (* TODO *)
      admit.
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
      destruct Heval as [k' [e1' [t1' [l1 [a2 [a3 [H1 [H2 [H3 [H4 H5]]]]]]]]]].
      assert (H2': eval_kl (k', l) L P pc e t1 (Atom (VClos e1' t1') l1)) by
          (apply IHn; try omega; assumption).
      assert (H3': eval_kl (k', l) L P pc e t2 a2) by
          (apply IHn; try omega; assumption).
      assert (H4': eval_kl (k', l) L P l1 (a2 :: e1') t1' a3) by
          (apply IHn; try omega; assumption).
      clear H2; clear H3; clear H4; subst.
      apply (eval_kl_app k' l L P pc e t1 t2 e1' t1' l1 a2 a3); assumption.
    + (* TDecl *)
      (* TODO *)
      admit.
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
  intros k l. apply (eval_kl_subset_n (S (k + l))). auto.
Qed.
  
End NI.

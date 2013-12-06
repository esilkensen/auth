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
      apply eval_kl_nat_inv in Heval. subst.
      apply eval_kl_nat.
    + (* TVar *)
      apply eval_kl_var_inv in Heval. destruct Heval as [v' [l' [H1 H2]]].
      subst. apply eval_kl_var. assumption.
    + (* TAbs *)
      apply eval_kl_abs_inv in Heval.
      subst. apply eval_kl_abs.
    + (* TApp *)
      admit.
    + (* TDecl *)
      admit.
  - destruct t.
    + (* TBool *)
      apply eval_kl_bool_inv in Heval.
      subst. apply eval_kl_bool.
    + (* TNat *)
      apply eval_kl_nat_inv in Heval.
      subst. apply eval_kl_nat.
    + (* TVar *)
      apply eval_kl_var_inv in Heval. destruct Heval as [v' [l' [H1 H2]]].
      subst. apply eval_kl_var. assumption.
    + (* TAbs *)
      apply eval_kl_abs_inv in Heval.
      subst. apply eval_kl_abs.
    + (* TApp *)
      admit.
    + (* TDecl *)
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

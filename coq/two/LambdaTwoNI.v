Require Import Program.Tactics.
Require Import LambdaTwo.

Section NI.

Theorem non_interference_strong_observer :
  forall L (P : value -> value -> Prop) k pc e1 e2 t a1 a2,
    (forall x, P x x) ->
    env_LPequiv L P e1 e2 ->
    eval L P pc e1 t a1 k ->
    eval L P pc e2 t a2 k ->
    atom_LPequiv L P a1 a2.
Proof.
  intros L P k.
  induction k as [| k'];
    intros pc e1 e2 t a1 a2 Prefl He Heval1 Heval2.
  - destruct t; unfold eval in *; subst; auto.
    + (* TNat *)
      destruct L; destruct pc.
      * right. left. auto.
      * left. auto.
      * right. right. auto.
      * right. right. auto.
    + (* TVar *)
      remember (atIndex e1 n) as o. remember (atIndex e2 n) as o'.
      destruct o as [a |]; destruct o' as [a' |]; auto.
      destruct a as [v1 l1]. destruct a' as [v2 l2]. subst.
      assert (atom_LPequiv L P (Atom v1 l1) (Atom v2 l2)) by
          (eapply list_forall2_atIndex; eauto).
      assert (l2 = l1) by
          (apply atom_LPequiv_lab_inv in H; auto). subst.
      destruct pc.
      * rewrite join_bot. assumption.
      * rewrite join_top. destruct l1; try assumption.
        apply atom_LPequiv_raise; assumption.
    + (* TLam *)
      destruct L; destruct pc.
      * right. left. auto.
      * left. auto.
      * right. right. auto.
      * right. right. auto.
  - admit.
Qed.

Theorem non_interference :
  forall L (P : value -> value -> Prop) k pc e1 e2 t a1 a2,
    (forall x, P x x) ->
    env_LPequiv L P e1 e2 ->
    eval L P pc e1 t a1 k ->
    eval L P pc e2 t a2 k ->
    atom_Lequiv L a1 a2.
Proof.
  intros L P k pc e1 e2 t a1 a2 Prefl He Heval1 Heval2.
  eapply non_interference_strong_observer in Heval2; eauto.
  eapply atom_LPequiv_Lequiv. eassumption.
Qed.
  
End NI.

Require Import Program.Tactics.
Require Import LambdaTwo.
Require Import LibTactics.

Section NI.

Lemma non_interference_nat :
  forall L P k pc e1 e2 t a1 a2,
    forall n,
      t = TNat n ->
      env_LPequiv L P e1 e2 ->
      eval L P pc e1 t k a1 ->
      eval L P pc e2 t k a2 ->
      (forall x, P x x) ->
      atom_LPequiv L P a1 a2.
Proof.
  introv Ht He Heval1 Heval2 Prefl. subst.
  assert (Ha1: a1 = (Atom (VNat n) pc)) by (eapply eval_nat_inv; eauto).
  assert (Ha2: a2 = (Atom (VNat n) pc)) by (eapply eval_nat_inv; eauto).
  destruct L; destruct pc; subst.
  - right. left. auto.
  - left. auto.
  - right. right. auto.
  - right. right. auto.
Qed.

Lemma non_interference_var :
  forall L P k pc e1 e2 t a1 a2,
    forall n,
      t = TVar n ->
      env_LPequiv L P e1 e2 ->
      eval L P pc e1 t k a1 ->
      eval L P pc e2 t k a2 ->
      (forall x, P x x) ->
      atom_LPequiv L P a1 a2.
Proof.
  introv Ht He Heval1 Heval2 Prefl. subst.
  remember (atIndex e1 n) as o1.
  remember (atIndex e2 n) as o2.
  destruct o1 as [[v1 l1] |];
  destruct o2 as [[v2 l2] |].
  - assert (atom_LPequiv L P (Atom v1 l1) (Atom v2 l2)) by
        (eapply list_forall2_atIndex; eauto).
    assert (l2 = l1) by
        (apply atom_LPequiv_lab_inv in H; auto). subst.
    destruct k; unfold eval in Heval1; unfold eval in Heval2;
    repeat (rewrite <- Heqo1 in Heval1; rewrite <- Heqo2 in Heval2; subst;
            destruct pc; [
              rewrite join_bot; assumption |
              rewrite join_top; destruct l1; try assumption;
              apply atom_LPequiv_raise; auto
           ]).
  - destruct k; unfold eval in Heval2;
    rewrite <- Heqo2 in Heval2; inversion Heval2.
  - destruct k; unfold eval in Heval1;
    rewrite <- Heqo1 in Heval1; inversion Heval1.
  - destruct k; unfold eval in Heval1;
    rewrite <- Heqo1 in Heval1; inversion Heval1.
Qed.

Lemma non_interference_abs :
  forall L P k pc e1 e2 t a1 a2,
    forall t',
      t = TAbs t' ->
      env_LPequiv L P e1 e2 ->
      eval L P pc e1 t k a1 ->
      eval L P pc e2 t k a2 ->
      (forall x, P x x) ->
      atom_LPequiv L P a1 a2.
Proof.
  introv Ht He Heval1 Heval2 Prefl. subst.
  assert (Ha1: a1 = (Atom (VClos e1 t') pc)) by (eapply eval_abs_inv; eauto).
  assert (Ha2: a2 = (Atom (VClos e2 t') pc)) by (eapply eval_abs_inv; eauto).
  destruct L; destruct pc; subst.
  - right. left. auto.
  - left. auto.
  - right. right. auto.
  - right. right. auto.
Qed.

Theorem non_interference_strong_observer :
  forall L (P : value -> value -> Prop) k pc e1 e2 t a1 a2,
    (forall x, P x x) ->
    env_LPequiv L P e1 e2 ->
    eval L P pc e1 t k a1 -> 
    eval L P pc e2 t k a2 -> 
    atom_LPequiv L P a1 a2.
Proof.
  Admitted.

Theorem non_interference :
  forall L (P : value -> value -> Prop) k pc e1 e2 t a1 a2,
    (forall x, P x x) ->
    env_LPequiv L P e1 e2 ->
    eval L P pc e1 t k a1 ->
    eval L P pc e2 t k a2 ->
    atom_Lequiv L a1 a2.
Proof.
  intros L P k pc e1 e2 t a1 a2 Prefl He Heval1 Heval2.
  eapply non_interference_strong_observer in Heval2; eauto.
  eapply atom_LPequiv_Lequiv. eassumption.
Qed.
  
End NI.

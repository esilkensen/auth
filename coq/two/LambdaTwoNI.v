Require Import Program.Tactics.
Require Import LambdaTwo.

Section NI.

Theorem non_interference_strong_observer :
  forall L (P : value -> value -> Prop) k pc e1 e2 t a1 a2,
    (forall x, P x x) ->
    env_LPequiv L P e1 e2 ->
    eval L P pc e1 t k a1 -> 
    eval L P pc e2 t k a2 -> 
    atom_LPequiv L P a1 a2.
Proof.
  intros L P k pc e1 e2 t a1 a2 Prefl He Heval1 Heval2.
  generalize dependent a2.
  generalize dependent e2.
  functional induction (eval L P pc e1 t k a1);
    simpl; auto; intros; subst.
  - (* E_Nat *)
    destruct L; destruct pc.
    + right. left. auto.
    + left. auto.
    + right. right. auto.
    + right. right. auto.
  - (* E_Var *)
    remember (atIndex e2 n) as o2. destruct o2 as [[v' l'] |].
    + assert (atom_LPequiv L P (Atom v l) (Atom v' l')) by
          (eapply list_forall2_atIndex; eauto).
      assert (l' = l) by
          (destruct H; destruct H; destruct_conjs; subst; auto).
      destruct pc; destruct l; subst; auto.
      apply atom_LPequiv_raise; auto.
    + inversion Heval2.
  - (* E_Abs *)
    destruct L; destruct pc.
    + right. left. auto.
    + left. auto.
    + right. right. auto.
    + right. right. auto.
Qed.

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

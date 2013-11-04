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

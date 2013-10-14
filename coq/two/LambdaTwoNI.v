Require Import MyTactics.
Require Import LabelAlgebra.
Require Import LambdaTwo.
Require Import TermEquivTwo.
Require Import IndistinguishabilityTwo.

Set Implicit Arguments.

Section NI.

Context (lab : two) (P : value -> value -> Prop).
  
(** * Preliminary lemmas. *)
(** ** The pc label is below the label of the resulting atom. *)
Lemma eval_pc_lower_bound :
  forall pc e t v l,
    pc; e ⊢ t ⇓ Atom v l ->
    pc ⊑ l.
Proof.
  Admitted.

(** ** Strong version of the non-interference theorem. *)
Lemma NI_strong :
  forall pc1 pc2 e1 e2 t1 t2 a1 a2,
    pc1 =L pc2 ->
    env_Lequiv lab P e1 e2 ->
    term_equiv t1 t2 ->
    pc1; e1 ⊢ t1 ⇓ a1 ->
    pc2; e2 ⊢ t2 ⇓ a2 ->
    atom_Lequiv lab P a1 a2.
Proof.
  Admitted.

(** * General non-interference theorem. *)
Theorem general_non_interference :
  forall pc e1 e2 t a1 a2,
    env_Lequiv lab P e1 e2 ->
    pc; e1 ⊢ t ⇓ a1 ->
    pc; e2 ⊢ t ⇓ a2 ->
    atom_Lequiv lab P a1 a2.
Proof.
  Admitted.

End NI.

Require Import Classical.
Require Import Program.Tactics.
Require Import MyTactics.
Require Import LabelAlgebra.
Require Import LambdaSyntax.

Section Indistinguishability.

Context (L : Type)
        (M : LabelAlgebra unit L)
        (l : L)
        (P : value L -> value L -> Prop)
        (Prefl : forall v, P v v).

Fixpoint atom_LPequiv a1 a2 : Prop :=
  match a1, a2 with
    | Atom v1 l1, Atom v2 l2 =>
      ((l1 ⊑ l \/ l2 ⊑ l) ->
       (value_LPequiv v1 v2 /\ l1 =L l2)) /\
      ((~ (l1 ⊑ l \/ l2 ⊑ l) /\ l ⊑ l1 /\ l ⊑ l2) ->
       match v1, v2 with
         | VNat n1, VNat n2 => P v1 v2
         | VClos e1 t1, VClos e2 t2 => value_LPequiv v1 v2
         | _, _ => True
       end)
  end
with value_LPequiv v1 v2 : Prop :=
       match v1, v2 with
         | VBool b1, VBool b2 => b1 = b2
         | VNat n1, VNat n2 => n1 = n2
         | VClos e1 t1, VClos e2 t2 =>
           list_forall2 atom_LPequiv e1 e2 /\ t1 = t2
         | VBool _, _ | VNat _, _ | VClos _ _, _ => False
       end.

Definition env_LPequiv : env L -> env L -> Prop :=
  list_forall2 atom_LPequiv.

Lemma atom_value_env_LPequiv_refl :
  (forall a, atom_LPequiv a a) /\
  (forall v, value_LPequiv v v) /\
  (forall e, env_LPequiv e e).
Proof.
  apply atom_value_env_mutind.
  - intros v Hv l1. 
    split; intro.
    + split; auto.
    + destruct v; auto.
  - intros b.
    unfold value_LPequiv. auto.
  - intros n.
    unfold value_LPequiv. auto.
  - intros e He t.
    unfold value_LPequiv. auto.
  - intros e Ha.
    unfold env_LPequiv.
    induction e as [| a e'].
    + reflexivity.
    + split.
      * apply (Ha 0). reflexivity.
      * apply IHe'. intros. apply (Ha (S n)). auto.
Qed.

Lemma atom_LPequiv_refl :
  forall a, atom_LPequiv a a.
Proof. apply atom_value_env_LPequiv_refl. Qed.

Lemma value_LPequiv_refl :
  forall v, value_LPequiv v v.
Proof. apply atom_value_env_LPequiv_refl. Qed.

Lemma env_LPequiv_refl :
  forall e, env_LPequiv e e.
Proof. apply atom_value_env_LPequiv_refl. Qed.

Lemma atom_LPequiv_raise :
  forall v1 l1 v2 l2 l',
    ((l1 ⊑ l \/ l ⊑ l1) /\ (l2 ⊑ l \/ l ⊑ l2)) ->
    atom_LPequiv (Atom v1 l1) (Atom v2 l2) ->
    atom_LPequiv (Atom v1 (l1 ⊔ l')) (Atom v2 (l2 ⊔ l')).
Proof.
  intros v1 l1 v2 l2 l' Htotal H.
  destruct Htotal as [Htotal1 Htotal2].
  destruct H as [Ha Hb].
  split; intro H1.
  - assert (H1': l1 ⊑ l \/ l2 ⊑ l)
      by (destruct H1; [
            left; transitivity (l1 ⊔ l'); auto |
            right; transitivity (l2 ⊔ l'); auto
         ]).
    apply Ha in H1'.
    destruct H1'; split; try apply labEquiv_join; auto.
  - destruct Htotal1 as [Htotal1 | Htotal1];
    destruct Htotal2 as [Htotal2 | Htotal2].
    + assert (H2: l1 ⊑ l \/ l2 ⊑ l) by auto.
      apply Ha in H2. destruct H2 as [H2a H2b].
      destruct v1; destruct v2; auto.
      inversion H2a; auto.
    + assert (H2: l1 ⊑ l \/ l2 ⊑ l) by auto.
      apply Ha in H2. destruct H2 as [H2a H2b].
      destruct v1; destruct v2; auto.
      inversion H2a; auto.
    + assert (H2: l1 ⊑ l \/ l2 ⊑ l) by auto.
      apply Ha in H2. destruct H2 as [H2a H2b].
      destruct v1; destruct v2; auto.
      inversion H2a; auto.
    + assert (H2: (l1 ⊑ l \/ l2 ⊑ l) \/ ~ (l1 ⊑ l \/ l2 ⊑ l)) by apply classic.
      destruct H2 as [H2 | H2].
      * apply Ha in H2. destruct H2 as [H2a H2b].
        destruct v1; destruct v2; auto.
        inversion H2a; auto.
      * apply Hb; auto.
Qed.

End Indistinguishability.

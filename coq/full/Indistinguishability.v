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
      ((l1 ⊑ l \/ l2 ⊑ l) /\
       value_LPequiv v1 v2 /\ l1 =L l2) \/
      (l ⊑ l1 /\ l ⊑ l2 /\ ~ l1 ⊑ l /\ ~ l2 ⊑ l /\
       match v1, v2 with
         | VNat n1, VNat n2 => P v1 v2
         | VClos e1 t1, VClos e2 t2 => value_LPequiv v1 v2
         | _, _ => True
       end) \/
      ~ (l1 ⊑ l \/ l ⊑ l1 \/ l2 ⊑ l \/ l ⊑ l2)
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
    assert (H1: l1 ⊑ l \/ ~ l1 ⊑ l) by apply classic.
    assert (H2: l ⊑ l1 \/ ~ l ⊑ l1) by apply classic.
    destruct v as [b | n | e t];
      (destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2]; [
         left; auto |
         left; auto |
         right; left; splits; auto |
         right; right; intro C; destruct C as [C | [C | [C | C]]]; auto
       ]).
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

End Indistinguishability.

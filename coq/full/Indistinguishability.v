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
        (Psym : forall v1 v2, P v1 v2 -> P v2 v1)
        (Prefl : forall v, P v v)
        (Ptrans : forall v1 v2 v3, P v1 v2 -> P v2 v3 -> P v1 v3).

Definition lab_Lequiv l1 l2 : Prop :=
  (~ l1 ⊑ l /\ ~ l2 ⊑ l) \/
  (l1 ⊑ l /\ l1 =L l2).

Fixpoint atom_LPequiv a1 a2 : Prop :=
  match a1, a2 with
    | Atom v1 l1, Atom v2 l2 =>
      (~ l1 ⊑ l /\ ~ l2 ⊑ l /\
       match v1, v2 with
         | VNat n1, VNat n2 => P v1 v2
         | VClos e1 t1, VClos e2 t2 => value_LPequiv v1 v2
         | _, _ => True
       end) \/
      (l1 ⊑ l /\ l1 =L l2 /\ value_LPequiv v1 v2)
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

Lemma labEquiv_lab_Lequiv :
  forall l1 l2,
    l1 =L l2 ->
    lab_Lequiv l1 l2.
Proof.
  intros l1 l2 H.
  inversion H as [H1 H2].
  assert (H3: (l1 ⊑ l \/ l2 ⊑ l) \/ ~ (l1 ⊑ l \/ l2 ⊑ l)) by apply classic.
  destruct H3 as [H3 | H3].
  - destruct H3 as [H3 | H3].
    + right. simpl. auto.
    + right. simpl. splits; try transitivity l2; auto.
  - assert (H4: ~ l1 ⊑ l /\ ~ l2 ⊑ l) by auto.
    destruct H4 as [H4 H5].
    left. auto.
Qed.

Lemma lab_Lequiv_refl :
  forall l1, lab_Lequiv l1 l1.
Proof.
  intros l1.
  assert (H1: l1 ⊑ l \/ ~ l1 ⊑ l) by apply classic.
  destruct H1 as [H1 | H1].
  - right. auto.
  - left. auto.
Qed.

Lemma lab_Lequiv_sym :
  forall l1 l2,
    lab_Lequiv l1 l2 ->
    lab_Lequiv l2 l1.
Proof.
  intros l1 l2 H.
  destruct H as [[H1 H2] | [H1 [H2 H3]]].
  - left. auto.
  - right. simpl. split; try transitivity l1; auto.
Qed.

Lemma lab_Lequiv_trans :
  forall l1 l2 l3,
    lab_Lequiv l1 l2 ->
    lab_Lequiv l2 l3 ->
    lab_Lequiv l1 l3.
Proof.
  intros l1 l2 l3 H1 H2.
  destruct H1 as [[H1a H1b] | [H1a [H1b H1c]]];
    destruct H2 as [[H2a H2b] | [H2a [H2b H2c]]].
  - left. auto.
  - contradiction.
  - contradict H2a. transitivity l1; auto.
  - right. simpl. splits; try transitivity l2; auto.
Qed.

Global Instance Equivalence_lab_Lequiv : Equivalence lab_Lequiv.
Proof.
  constructor.
  - unfold Reflexive. apply lab_Lequiv_refl.
  - unfold Symmetric. apply lab_Lequiv_sym.
  - unfold Transitive. apply lab_Lequiv_trans.
Qed.

Lemma lab_Lequiv_join :
  forall l1 l2 l1' l2',
    lab_Lequiv l1 l2 ->
    lab_Lequiv l1' l2' ->
    lab_Lequiv (l1 ⊔ l1') (l2 ⊔ l2').
Proof.
  intros l1 l2 l1' l2' H1 H2. 
  destruct H1 as [[H1a H1b] | [H1a [H1b H1c]]];
    destruct H2 as [[H2a H2b] | [H2a [H2b H2c]]].
  - left. split; intro C.
    + contradict H1a.
      assert (H3: l1 ⊑ l1 ⊔ l1') by auto.
      transitivity (l1 ⊔ l1'); auto.
    + contradict H1b.
      assert (H3: l2 ⊑ l2 ⊔ l2') by auto.
      transitivity (l2 ⊔ l2'); auto.
  - left. split; intro C.
    + contradict H1a.
      assert (H3: l1 ⊑ l1 ⊔ l1') by auto.
      transitivity (l1 ⊔ l1'); auto.
    + contradict H1b.
      assert (H3: l2 ⊑ l2 ⊔ l2') by auto.
      transitivity (l2 ⊔ l2'); auto.
  - left. split; intro C.
    + contradict H2a.
      assert (H3: l1' ⊑ l1 ⊔ l1') by auto.
      transitivity (l1 ⊔ l1'); auto.
    + contradict H2b.
      assert (H3: l2' ⊑ l2 ⊔ l2') by auto.
      transitivity (l2 ⊔ l2'); auto.
  - assert (H3: l1 ⊑ l2 ⊔ l2') by (transitivity l2; auto).
    assert (H4: l1' ⊑ l2 ⊔ l2') by (transitivity l2'; auto).
    assert (H5: l2 ⊑ l1 ⊔ l1') by (transitivity l1; auto).
    assert (H6: l2' ⊑ l1 ⊔ l1') by (transitivity l1'; auto).
    right. simpl. splits; auto.
Qed.

Lemma atom_value_env_LPequiv_refl :
  (forall a, atom_LPequiv a a) /\
  (forall v, value_LPequiv v v) /\
  (forall e, env_LPequiv e e).
Proof.
  apply atom_value_env_mutind.
  - intros v Hv l1.
    assert (H1: l1 ⊑ l \/ ~ l1 ⊑ l) by apply classic.
    destruct H1 as [H1 | H1].
    + right. auto.
    + left. destruct v; auto.
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

Lemma atom_LPequiv_lab_Lequiv_refl :
  forall v l1 l2,
    lab_Lequiv l1 l2 ->
    atom_LPequiv (Atom v l1) (Atom v l2).
Proof.
  intros v l1 l2 Hlab.
  destruct Hlab as [[Hlab1 Hlab2] | [Hlab1 Hlab2]].
  - left. destruct v; splits; auto. apply value_LPequiv_refl.
  - right. splits; auto. apply value_LPequiv_refl.
Qed.

Lemma or_sym :
  forall p q, p \/ q -> q \/ p.
Proof.
  intros p q H. 
  destruct H as [H | H].
  - right. assumption.
  - left. assumption.
Qed.

Lemma atom_value_env_LPequiv_sym :
  (forall a1 a2, atom_LPequiv a1 a2 -> atom_LPequiv a2 a1) /\
  (forall v1 v2, value_LPequiv v1 v2 -> value_LPequiv v2 v1) /\
  (forall e1 e2, env_LPequiv e1 e2 -> env_LPequiv e2 e1).
Proof.
  apply atom_value_env_mutind.
  - intros v1 Hv l1 a2 H; destruct a2 as [v2 l2].
    destruct H as [[H1 [H2 H3]] | [H1 [[H2 H3] H4]]].
    + left. destruct v1; destruct v2; auto.
    + right. simpl. splits; try transitivity l1; auto.
  - intros b1 v2 H.
    destruct v2 as [b2 | n2 | e2 t2]; inversion H; reflexivity.
  - intros n1 v2 H.
    destruct v2 as [b2 | n2 | e2 t2]; inversion H; reflexivity.
  - intros e1 He t1 v2 H.
    destruct v2 as [b2 | n2 | e2 t2]; inversion H; subst.
    split.
    + apply He. assumption.
    + reflexivity.
  - intro e1.
    unfold env_LPequiv.
    induction e1 as [| a1 e1']; intros Ha e2 H.
    + destruct e2 as [| a2 e2']; inversion H; reflexivity.
    + destruct e2 as [| a2 e2']; inversion H.
      split.
      * apply (Ha 0). reflexivity. assumption.
      * apply IHe1'. intros. apply (Ha (S n)); auto. assumption.
Qed.

Lemma atom_LPequiv_sym :
  forall a1 a2, atom_LPequiv a1 a2 -> atom_LPequiv a2 a1.
Proof. apply atom_value_env_LPequiv_sym. Qed.

Lemma value_LPequiv_sym :
  forall v1 v2, value_LPequiv v1 v2 -> value_LPequiv v2 v1.
Proof. apply atom_value_env_LPequiv_sym. Qed.

Lemma env_LPequiv_sym :
  forall e1 e2, env_LPequiv e1 e2 -> env_LPequiv e2 e1.
Proof. apply atom_value_env_LPequiv_sym. Qed.

Lemma atom_LPequiv_lab_inv :
  forall v1 l1 v2 l2,
    atom_LPequiv (Atom v1 l1) (Atom v2 l2) ->
    lab_Lequiv l1 l2.
Proof.
  intros v1 l1 v2 l2 H.
  destruct H as [[H1 [H2 H3]] | [H1 [[H2 H3] H4]]].
  - left. auto.
  - right. simpl. auto.
Qed.

Lemma atom_LPequiv_raise :
  forall v1 l1 v2 l2 l',
    l1 ⊑ l' -> l2 ⊑ l' ->
    atom_LPequiv (Atom v1 l1) (Atom v2 l2) ->
    atom_LPequiv (Atom v1 l') (Atom v2 l').
Proof.
  intros v1 l1 v2 l2 l' H1 H2 Ha.
  destruct Ha as [[Ha1 [Ha2 Ha3]] | [Ha1 [[Ha2 Ha3] Ha4]]].
  - left. splits.
    + intro C. contradict Ha1. transitivity l'; auto.
    + intro C. contradict Ha1. transitivity l'; auto.
    + destruct v1; destruct v2; auto.
  - assert (H3: l' ⊑ l \/ ~ l' ⊑ l) by apply classic.
      destruct H3 as [H3 | H3].
      * right. auto.
      * left. splits; destruct v1; destruct v2; inversion Ha4; auto.
Qed.

Lemma atom_LPequiv_labEquiv_left :
  forall v1 l1 v2 l2 l1',
    l1 =L l1' ->
    atom_LPequiv (Atom v1 l1) (Atom v2 l2) ->
    atom_LPequiv (Atom v1 l1') (Atom v2 l2).
Proof.
  intros v1 l1 v2 l2 l1' H1 H2.
  inversion H1 as [H1a H1b].
  destruct H2 as [[H2a [H2b H2c]] | [H2a [[H2b H2c] H2d]]].
  - left. splits.
    + intro C. contradict H2a. transitivity l1'; auto.
    + intro C. contradiction.
    + destruct v1; destruct v2; auto.
  - right. splits.
    + transitivity l1; auto.
    + split; transitivity l1; auto.
    + assumption.
Qed.

Lemma atom_LPequiv_labEquiv_right :
  forall v1 l1 v2 l2 l2',
    l2 =L l2' ->
    atom_LPequiv (Atom v1 l1) (Atom v2 l2) ->
    atom_LPequiv (Atom v1 l1) (Atom v2 l2').
Proof.
  intros v1 l1 v2 l2 l2' H1 H2.
  assert (H3: atom_LPequiv (Atom v2 l2) (Atom v1 l1))
    by (apply atom_LPequiv_sym; assumption).
  assert (H4: atom_LPequiv (Atom v2 l2') (Atom v1 l1))
    by (apply (atom_LPequiv_labEquiv_left v2 l2 v1 l1 l2');
        assumption).
  apply atom_LPequiv_sym. assumption.
Qed.

Lemma atom_LPequiv_labEquiv :
  forall v1 l1 v2 l2 l1' l2',
    l1 =L l1' ->
    l2 =L l2' ->
    atom_LPequiv (Atom v1 l1) (Atom v2 l2) ->
    atom_LPequiv (Atom v1 l1') (Atom v2 l2').
Proof.
  intros v1 l1 v2 l2 l1' l2' H1 H2 H3.
  assert (H4: atom_LPequiv (Atom v1 l1') (Atom v2 l2))
    by (apply (atom_LPequiv_labEquiv_left v1 l1 v2 l2 l1');
        assumption).
  apply (atom_LPequiv_labEquiv_right v1 l1' v2 l2 l2');
    assumption.
Qed.

Lemma atom_LPequiv_lab_Lequiv_raise :
  forall v1 l1 v2 l2 l1' l2',
    lab_Lequiv l1' l2' ->
    atom_LPequiv (Atom v1 l1) (Atom v2 l2) ->
    atom_LPequiv (Atom v1 (l1 ⊔ l1')) (Atom v2 (l2 ⊔ l2')).
Proof.
  intros v1 l1 v2 l2 l1' l2' Hlab Ha.
  destruct Ha as [[Ha1 [Ha2 Ha3]] | [Ha1 [[Ha2 Ha3] Ha4]]].
  - destruct Hlab as [[Hlab1 Hlab2] | [Hlab1 [Hlab2 Hlab3]]]; left;
    (splits; [
       intro C; contradict Ha1; transitivity (l1 ⊔ l1'); auto |
       intro C; contradict Ha2; transitivity (l2 ⊔ l2'); auto |
       destruct v1; destruct v2; auto
     ]).
  - destruct Hlab as [[Hlab1 Hlab2] | [Hlab1 [Hlab2 Hlab3]]].
    + left. splits.
      * intro C. contradict Hlab1. transitivity (l1 ⊔ l1'); auto.
      * intro C. contradict Hlab2. transitivity (l2 ⊔ l2'); auto.
      * destruct v1; destruct v2; inversion Ha4; auto.
    + right. simpl. splits; auto.
      * assert (H1: l1 ⊑ l2 ⊔ l2') by (transitivity l2; auto).
        assert (H2: l1' ⊑ l2 ⊔ l2') by (transitivity l2'; auto).
        auto.
      * assert (H1: l2 ⊑ l1 ⊔ l1') by (transitivity l1; auto).
        assert (H2: l2' ⊑ l1 ⊔ l1') by (transitivity l1'; auto).
        auto.
Qed.

End Indistinguishability.

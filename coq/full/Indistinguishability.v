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
        (Ptrans : forall v1 v2 v3, P v1 v2 -> P v2 v3 -> P v1 v3)
        (Ltotal : forall l l', l ⊑ l' \/ l' ⊑ l).

Definition lab_Lequiv l1 l2 : Prop :=
  ((l1 ⊑ l \/ l2 ⊑ l) /\ l1 =L l2) \/
  ~ (l1 ⊑ l \/ l2 ⊑ l) /\ l ⊑ l1 /\ l ⊑ l2.

Definition lab_Lequiv' l1 l2 : Prop :=
  (~ l1 ⊑ l /\ ~ l2 ⊑ l) \/
  (l1 ⊑ l /\ l1 =L l2).

Lemma lab_Lequiv_Lequiv' :
  forall l1 l2,
    lab_Lequiv l1 l2 <-> lab_Lequiv' l1 l2.
Proof.
  intros l1 l2.
  unfold lab_Lequiv.
  unfold lab_Lequiv'.
  split; simpl; intro H.
  - destruct H as [H | H].
    + destruct H as [[H1 | H1] [H2 H3]]; right; auto.
      split; try transitivity l2; auto.
    + destruct H as [H1 [H2 H3]].
      assert (H4: ~ l1 ⊑ l /\ ~ l2 ⊑ l) by auto.
      destruct H4 as [H4a H4b].
      left. auto.
  - destruct H as [H | H].
    + destruct H as [H1 H2].
      assert (H3: l ⊑ l1 \/ l1 ⊑ l) by auto.
      assert (H4: l ⊑ l2 \/ l2 ⊑ l) by auto.
      destruct H3 as [H3 | H3]; destruct H4 as [H4 | H4]; try contradiction.
      right. split. intro C. destruct C; contradiction. auto.
    + destruct H as [H1 [H2 H3]].
      left. auto.
Qed.

Fixpoint atom_LPequiv a1 a2 : Prop :=
  match a1, a2 with
    | Atom v1 l1, Atom v2 l2 =>
      ((l1 ⊑ l \/ l2 ⊑ l) ->
       (value_LPequiv v1 v2 /\ lab_Lequiv l1 l2)) /\
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

Fixpoint atom_LPequiv' a1 a2 : Prop :=
  match a1, a2 with
    | Atom v1 l1, Atom v2 l2 =>
      (~ l1 ⊑ l /\ ~ l2 ⊑ l /\
       match v1, v2 with
         | VNat n1, VNat n2 => P v1 v2
         | VClos e1 t1, VClos e2 t2 => value_LPequiv v1 v2
         | _, _ => True
       end) \/
      (l1 ⊑ l /\ l1 =L l2 /\ value_LPequiv v1 v2)
  end.

Lemma atom_LPequiv_LPequiv' :
  forall a1 a2,
    atom_LPequiv a1 a2 <-> atom_LPequiv' a1 a2.
Proof.
  intros a1 a2.
  destruct a1 as [v1 l1].
  destruct a2 as [v2 l2].
  split; intro H.
  - destruct H as [Ha Hb].
    assert (H1: l1 ⊑ l \/ l ⊑ l1) by auto.
    destruct H1 as [H1 | H1].
    + assert (H2: l1 ⊑ l \/ l2 ⊑ l) by auto.
      apply Ha in H2. destruct H2 as [H2a H2b].
      destruct H2b as [[H2b H2c] | [H2b [H2c H2d]]].
      * right. auto.
      * contradict H1. auto.
    + assert (H2: l2 ⊑ l \/ l ⊑ l2) by auto.
      destruct H2 as [H2 | H2].
      * assert (H3: l1 ⊑ l \/ l2 ⊑ l) by auto.
        apply Ha in H3. destruct H3 as [H3a H3b].
        inversion H3b as [[H3c [H3d H3e]] | [H3c [H3d H3e]]].
        right. split. transitivity l2; auto. split. auto. split; auto. auto.
        contradict H2. auto.
      * assert (H3: l1 ⊑ l \/ ~ l1 ⊑ l) by apply classic.
        assert (H4: l2 ⊑ l \/ ~ l2 ⊑ l) by apply classic.
        destruct H3 as [H3 | H3]; destruct H4 as [H4 | H4].
        assert (H5: l1 ⊑ l \/ l2 ⊑ l) by auto.
        apply Ha in H5. destruct H5 as [H5a H5b].
        right. splits; auto. split; transitivity l; auto.
        assert (H5: l1 ⊑ l \/ l2 ⊑ l) by auto.
        apply Ha in H5. destruct H5 as [H5a H5b].
        right. splits; auto.
        destruct H5b as [[H5b H5c] | [H5b [H5c H5d]]]; auto.
        split. transitivity l; auto. contradict H3. auto.
        assert (H5: l1 ⊑ l \/ l2 ⊑ l) by auto.
        apply Ha in H5. destruct H5 as [H5a H5b].
        inversion H5b as [[H5c [H5d H5e]] | [H5c [H5d H5e]]].
        contradict H3. transitivity l2; auto.
        contradict H4. auto.
        assert (H5: ~ (l1 ⊑ l \/ l2 ⊑ l) /\ l ⊑ l1 /\ l ⊑ l2)
          by (split; [ intro C; destruct C; contradiction | auto ]).
        apply Hb in H5. left. auto.
  - destruct H as [[H1 [H2 H3]] | [H1 [H2 H3]]].
    + split; intro H4.
      * destruct H4; contradiction.
      * destruct H4 as [H4a [H4b H4c]].
        destruct v1; destruct v2; auto.
    + split; intro H4.
      * split; auto. left. auto.
      * destruct H4 as [H4a [H4b H4c]].
        destruct v1; destruct v2; inversion H3; auto.
Qed.

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
  - left. auto.
  - assert (H4: ~ l1 ⊑ l /\ ~ l2 ⊑ l) by auto.
    destruct H4 as [H4 H5].
    assert (H4': l1 ⊑ l \/ l ⊑ l1) by auto.
    assert (H5': l2 ⊑ l \/ l ⊑ l2) by auto.
    destruct H4'; destruct H5'; try contradiction.
    right. auto.
Qed.

Lemma lab_Lequiv_refl :
  forall l1, lab_Lequiv l1 l1.
Proof.
  intros l1.
  assert (H1: l1 ⊑ l \/ ~ l1 ⊑ l) by apply classic.
  assert (H2: l1 ⊑ l \/ l ⊑ l1) by auto.
  destruct H1 as [H1 | H1].
  - left. auto.
  - right. split.
    + intro C. destruct C; contradiction.
    + destruct H2 as [H2 | H2].
      * contradiction.
      * auto.
Qed.

Lemma lab_Lequiv_sym :
  forall l1 l2,
    lab_Lequiv l1 l2 ->
    lab_Lequiv l2 l1.
Proof.
  intros l1 l2 H.
  destruct H as [[H1 [H2 H3]] | [H1 [H2 H3]]].
  - destruct H1 as [H1 | H1].
    + left. split.
      * right. assumption.
      * split; assumption.
    + left. split.
      * left. assumption.
      * split; assumption.
  - assert (H4: ~ l1 ⊑ l /\ ~ l2 ⊑ l) by auto.
    destruct H4 as [H4a H4b].
    assert (H5: l ⊑ l1)
      by (assert (H6: l1 ⊑ l \/ l ⊑ l1) by auto;
          destruct H6 as [H6 | H6]; try contradiction; assumption).
    assert (H6: ~ l2 ⊑ l /\ ~ l1 ⊑ l) by auto.
    assert (H7: ~ (l2 ⊑ l \/ l1 ⊑ l))
      by (intro C; destruct C; contradiction).
    right. split.
    + assumption.
    + split; assumption.
Qed.

Lemma lab_Lequiv_trans :
  forall l1 l2 l3,
    lab_Lequiv l1 l2 ->
    lab_Lequiv l2 l3 ->
    lab_Lequiv l1 l3.
Proof.
  intros l1 l2 l3 H1 H2.
  destruct H1 as [[H1a H1b] | [H1a H1b]];
    destruct H2 as [[H2a H2b] | [H2a H2b]];
    inversion H1b as [H3 H4];
    inversion H2b as [H5 H6].
  - left. split.
    + destruct H1a as [H1a | H1a].
      * left. assumption.
      * left. transitivity l2; assumption.
    + split; transitivity l2; assumption.
  - assert (H7: ~ l2 ⊑ l /\ ~ l3 ⊑ l) by auto;
    destruct H7 as [H7a H7b].
    assert (H8: l ⊑ l2)
      by (assert (H: l ⊑ l2 \/ l2 ⊑ l) by auto;
          destruct H; try contradiction; assumption).
    destruct H1a as [H1a | H1a].
    + contradict H7a. transitivity l1; assumption.
    + contradict H7a. assumption.
  - assert (H7: ~ l1 ⊑ l /\ ~ l2 ⊑ l) by auto;
    destruct H7 as [H7a H7b].
    assert (H8: l ⊑ l1)
      by (assert (H: l ⊑ l1 \/ l1 ⊑ l) by auto;
          destruct H; try contradiction; assumption).
    destruct H2a as [H2a | H2a].
    + contradict H7b. assumption.
    + contradict H7b. transitivity l3; assumption.
  - assert (H7: ~ l1 ⊑ l /\ ~ l2 ⊑ l) by auto;
    destruct H7 as [H7a H7b].
    assert (H8: ~ l3 ⊑ l) by auto.
    right. split.
    + intro C. destruct C; contradiction.
    + split; assumption.
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
  destruct H1 as [[H1a H1b] | [H1a H1b]];
    destruct H2 as [[H2a H2b] | [H2a H2b]].
  - inversion H1b as [H3 H4].
    inversion H2b as [H5 H6].
    left. split.
    + destruct H1a; destruct H2a.
      * left. auto.
      * left. assert (l1' ⊑ l) by (transitivity l2'; auto). auto.
      * left. assert (l1 ⊑ l) by (transitivity l2; auto). auto.
      * right. auto.
    + split.
      * assert (l1 ⊑ l2 ⊔ l2') by (transitivity l2; auto).
        assert (l1' ⊑ l2 ⊔ l2') by (transitivity l2'; auto). auto.
      * assert (l2 ⊑ l1 ⊔ l1') by (transitivity l1; auto).
        assert (l2' ⊑ l1 ⊔ l1') by (transitivity l1'; auto). auto.
  - inversion H1b as [H3 H4].
    inversion H2b as [H5 H6].
    assert (H5': ~ l2' ⊑ l) by auto.
    assert (H7: l ⊑ l1' \/ l1' ⊑ l) by auto.
    assert (H7': ~ l1' ⊑ l) by auto.
    destruct H7 as [H7 | H7]; try contradiction.
    destruct H1a as [H1a | H1a]; right;
    (splits; [
       intro C; (destruct C as [C | C]; [
                   contradict H7'; transitivity (l1 ⊔ l1'); auto |
                   contradict H5'; transitivity (l2 ⊔ l2'); auto
                ]) |
       transitivity l1'; auto |
       transitivity l2'; auto
     ]).
  - inversion H1b as [H3 H4].
    inversion H2b as [H5 H6].
    assert (H3': ~ l2 ⊑ l) by auto.
    assert (H4': ~ l1 ⊑ l) by auto.
    assert (H7: l ⊑ l1 \/ l1 ⊑ l) by auto.
    destruct H7 as [H7 | H7]; try contradiction.
    destruct H2a as [H2a | H2a]; right;
    (splits; [
       intro C; (destruct C as [C | C]; [
                   contradict H4'; transitivity (l1 ⊔ l1'); auto |
                   contradict H3'; transitivity (l2 ⊔ l2'); auto
                ]) |
       transitivity l1; auto |
       transitivity l2; auto
     ]).
  - inversion H1b as [H3 H4].
    inversion H2b as [H5 H6].
    assert (H7: l ⊑ l1 \/ l1 ⊑ l) by auto.
    assert (H8: l ⊑ l1' \/ l1' ⊑ l) by auto.
    assert (H4': ~ l2 ⊑ l) by auto.
    assert (H6': ~ l2' ⊑ l) by auto.
    assert (H3': ~ l1 ⊑ l) by auto.
    assert (H5': ~ l1' ⊑ l) by auto.
    destruct H7 as [H7 | H7];
      destruct H8 as [H8 | H8]; try contradiction.
    right. splits.
    * intro C; (destruct C as [C | C]; [
                  contradict H5'; transitivity (l1 ⊔ l1'); auto |
                  contradict H6'; transitivity (l2 ⊔ l2'); auto
                ]).
    * transitivity l1; auto.
    * transitivity l2; auto.
Qed.

Lemma atom_value_env_LPequiv_refl :
  (forall a, atom_LPequiv a a) /\
  (forall v, value_LPequiv v v) /\
  (forall e, env_LPequiv e e).
Proof.
  apply atom_value_env_mutind.
  - intros v Hv l1. 
    split; intro.
    + split. assumption. apply lab_Lequiv_refl.
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

Lemma atom_LPequiv_lab_Lequiv_refl :
  forall v l1 l2,
    lab_Lequiv l1 l2 ->
    atom_LPequiv (Atom v l1) (Atom v l2).
Proof.
  intros v l1 l2 Hlab.
  destruct Hlab as [[Hlab1 Hlab2] | [Hlab1 Hlab2]].
  - split; intro H1.
    + split.
      * apply value_LPequiv_refl.
      * left. auto.
    + destruct v; try apply value_LPequiv_refl; auto.
  - split; intro H1.
    + contradiction.
    + destruct v; try apply value_LPequiv_refl; auto.
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
    destruct H as [H1 H2].
    split; intro H3.
    + assert (H4: l1 ⊑ l \/ l2 ⊑ l) by (apply or_sym; assumption).
      apply H1 in H4. destruct H4 as [H4a H4b]. split.
      * apply Hv. assumption.
      * apply lab_Lequiv_sym. assumption.
    + destruct v2; destruct v1; auto.
      * destruct H3 as [H3a [H3b H3c]].
        assert (H4: ~ l2 ⊑ l /\ ~ l1 ⊑ l) by auto.
        destruct H4 as [H4a H4b].
        assert (H5: ~ l1 ⊑ l /\ ~ l2 ⊑ l) by auto.
        assert (H6: ~ (l1 ⊑ l \/ l2 ⊑ l))
          by (intro C; destruct C; contradiction).
        assert (H7: P (VNat L n0) (VNat L n))
          by (apply H2; split; [ assumption | split; assumption ]).
        apply Psym. assumption.
      * destruct H3 as [H3a [H3b H3c]].
        assert (H4: ~ l2 ⊑ l /\ ~ l1 ⊑ l) by auto.
        destruct H4 as [H4a H4b].
        assert (H5: ~ l1 ⊑ l /\ ~ l2 ⊑ l) by auto.
        assert (H6: ~ (l1 ⊑ l \/ l2 ⊑ l))
          by (intro C; destruct C; contradiction).
        assert (H7: value_LPequiv (VClos l3 t0) (VClos l0 t))
          by (apply H2; split; [ assumption | split; assumption ]).
        apply Hv. assumption.
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
  destruct H as [H1 H2].
  assert (H3: (l1 ⊑ l \/ l2 ⊑ l) \/ ~ (l1 ⊑ l \/ l2 ⊑ l)) by apply classic.
  destruct H3 as [H3 | H3].
  - apply H1 in H3. destruct H3 as [H3a H3b].
    assumption.
  - assert (H4: ~ l1 ⊑ l /\ ~ l2 ⊑ l) by auto.
    destruct H4 as [H4a H4b].
    assert (H5: l1 ⊑ l \/ l ⊑ l1) by auto.
    assert (H6: l2 ⊑ l \/ l ⊑ l2) by auto.
    destruct H5; destruct H6; try contradiction.
    right. auto.
Qed.

Lemma atom_LPequiv_raise :
  forall v1 l1 v2 l2 l',
    l1 ⊑ l' -> l2 ⊑ l' ->
    atom_LPequiv (Atom v1 l1) (Atom v2 l2) ->
    atom_LPequiv (Atom v1 l') (Atom v2 l').
Proof.
  intros v1 l1 v2 l2 l' H1 H2 Ha.
  inversion Ha as [Ha1 Ha2].
  split; intro H3.
  - assert (H4: value_LPequiv v1 v2 /\ lab_Lequiv l1 l2)
      by (apply Ha1; (destruct H3 as [H3 | H3]; [
                        left; transitivity l'; assumption |
                        right; transitivity l'; assumption
                      ])).
    destruct H4 as [H4a H4b].
    split. assumption. apply lab_Lequiv_refl.
  - assert (Hl: lab_Lequiv l1 l2) by (eapply atom_LPequiv_lab_inv; eauto).
    destruct Hl as [Hl | Hl].
    + assert (H4: value_LPequiv v1 v2 /\ lab_Lequiv l1 l2)
        by (apply Ha1; destruct Hl; assumption).
      destruct H4 as [H4a H4b].
      destruct v1; destruct v2; inversion H4a; auto.
    + destruct Hl as [H4 [H5 H6]].
      assert (H4a: ~ l1 ⊑ l) by auto.
      assert (H7: l ⊑ l1 \/ l1 ⊑ l) by auto.
      destruct H7 as [H7 | H7]; try contradiction.
      apply Ha2. auto.
Qed.

Lemma atom_LPequiv_labEquiv_left :
  forall v1 l1 v2 l2 l1',
    l1 =L l1' ->
    atom_LPequiv (Atom v1 l1) (Atom v2 l2) ->
    atom_LPequiv (Atom v1 l1') (Atom v2 l2).
Proof.
  intros v1 l1 v2 l2 l1' H1 H2.
  destruct H2 as [H2a H2b].
  split; intro H3.
  - assert (H4: l1 ⊑ l \/ l2 ⊑ l)
      by (inversion H1 as [H1a H1b];
          destruct H3 as [H3 | H3];
          [ left; transitivity l1'; assumption |
            right; assumption ]).
    apply H2a in H4. destruct H4 as [H4a H4b].
    split.
    + assumption.
    + destruct H4b as [[H4b H4c] | [H4b H4c]];
      inversion H1 as [H1a H1b];
      inversion H4c as [H4d H4e].
      * left. split. assumption. split; transitivity l1; assumption.
      * right. split. intro C.
        assert (H4b': ~ l1 ⊑ l /\ ~ l2 ⊑ l) by auto.
        destruct H4b' as [H5 H6].
        destruct C as [C | C].
        contradict H5. transitivity l1'; assumption.
        contradict H6. assumption.
        split. transitivity l1; auto. assumption.
  - destruct v1; destruct v2; try reflexivity;
    inversion H1 as [H1a H1b];
    destruct H3 as [H3a [H3b H3c]];
    assert (H4: ~ l1' ⊑ l /\ ~ l2 ⊑ l) by auto;
    destruct H4 as [H4a H4b]; apply H2b;
    (splits; [
       intro C;
       destruct C as [C | C]; [
         contradict H4a; transitivity l1; assumption |
         contradict H4b; assumption
       ] |
       transitivity l1'; assumption |
       assumption
     ]).
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
  destruct Ha as [Ha Hb].
  split; intro H1.
  - assert (H1': l1 ⊑ l \/ l2 ⊑ l)
      by (destruct H1; [
            left; transitivity (l1 ⊔ l1'); auto |
            right; transitivity (l2 ⊔ l2'); auto
         ]).
    apply Ha in H1'.
    destruct H1' as [H1'a H1'b].
    split. assumption. apply lab_Lequiv_join; assumption.
  - destruct v1; destruct v2; auto;
    assert (H1': (l1 ⊑ l \/ l2 ⊑ l) \/ ~ (l1 ⊑ l \/ l2 ⊑ l)) by apply classic;
    (destruct H1' as [H1' | H1']; [
       apply Ha in H1'; destruct H1' as [H1'a H1'b]; inversion H1'a; auto |
       assert (H2: ~ l1 ⊑ l /\ ~ l2 ⊑ l) by auto;
         destruct H2 as [H2a H2b];
         assert (H2a': l1 ⊑ l \/ l ⊑ l1) by auto;
         assert (H2b': l2 ⊑ l \/ l ⊑ l2) by auto;
         destruct H2a'; destruct H2b'; try contradiction;
         apply Hb; auto
     ]).
Qed.

End Indistinguishability.

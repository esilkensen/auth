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
        (Prefl : forall v, P v v)
        (Ltotal: forall l l', l ⊑ l' \/ l' ⊑ l).

Definition lab_Lequiv l1 l2 : Prop :=
  ((l1 ⊑ l \/ l2 ⊑ l) /\ l1 =L l2) \/
  ~ (l1 ⊑ l \/ l2 ⊑ l) /\ l ⊑ l2 /\ l ⊑ l2.

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
    inversion H2b as [H5 H6]; clear H6.
    assert (H5': ~ l2' ⊑ l) by auto.
    assert (H6: l ⊑ l1' \/ l1' ⊑ l) by auto.
    assert (H6': ~ l1' ⊑ l) by auto.
    destruct H6 as [H6 | H6]; try contradiction.
    destruct H1a as [H1a | H1a];
      right; (split; [
                intro C; (destruct C as [C | C]; [
                            contradict H6'; transitivity (l1 ⊔ l1'); auto |
                            contradict H5'; transitivity (l2 ⊔ l2'); auto
                          ]) |
                split; transitivity l2'; auto
              ]).
  - inversion H1b as [H3 H4]; clear H4.
    inversion H2b as [H4 H5].
    assert (H3': ~ l2 ⊑ l) by auto.
    assert (H6': ~ l1 ⊑ l) by auto.
    assert (H6: l ⊑ l1 \/ l1 ⊑ l) by auto.
    destruct H6 as [H6 | H6]; try contradiction.
    destruct H2a as [H2a | H2a];
      right; (split; [
                intro C; (destruct C as [C | C]; [
                            contradict H6'; transitivity (l1 ⊔ l1'); auto |
                            contradict H3'; transitivity (l2 ⊔ l2'); auto
                          ]) |
                split; transitivity l2; auto
              ]).
  - inversion H1b as [H3 H4]; clear H4.
    inversion H2b as [H4 H5]; clear H5.
    assert (H5: l ⊑ l1 \/ l1 ⊑ l) by auto.
    assert (H6: l ⊑ l1' \/ l1' ⊑ l) by auto.
    assert (H3': ~ l2 ⊑ l) by auto.
    assert (H4': ~ l2' ⊑ l) by auto.
    assert (H5': ~ l1 ⊑ l) by auto.
    assert (H6': ~ l1' ⊑ l) by auto.
    destruct H5 as [H5 | H5];
      destruct H6 as [H6 | H6]; try contradiction.
    right. split.
    + intro C. destruct C as [C | C].
      * contradict H5'. transitivity (l1 ⊔ l1'); auto.
      * contradict H3'. transitivity (l2 ⊔ l2'); auto.
    + split; transitivity l2; auto.
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
    + destruct Hl as [H4 [H5 H6]]; clear H6.
      assert (H4a: ~ l1 ⊑ l) by auto.
      assert (H6: l ⊑ l1 \/ l1 ⊑ l) by auto.
      destruct H6 as [H6 | H6]; try contradiction.
      apply Ha2. auto.
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

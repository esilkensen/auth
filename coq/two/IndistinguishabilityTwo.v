Require Import Program.Tactics. 
Require Import MyTactics.
Require Import LabelAlgebra.
Require Import LambdaTwoSyntax.

Section IndistinguishabilityTwo.

Context (L : two)
        (P : value -> value -> Prop)
        (Prefl : forall x, P x x).

Fixpoint atom_LPequiv a1 a2 : Prop :=
  match a1, a2 with
    | Atom v1 l1, Atom v2 l2 =>
      (L = Bottom2 /\ l1 = l2 /\ l1 = Top2 /\
       match v1, v2 with
         | VNat n1, VNat n2 => P v1 v2
         | VClos e1 t1, VClos e2 t2 => value_LPequiv v1 v2
         | _, _ => True
       end) \/
      (L = Bottom2 /\ l1 = l2 /\ l1 = Bottom2 /\ value_LPequiv v1 v2) \/
      (L = Top2 /\ l1 = l2 /\ value_LPequiv v1 v2)
  end
with value_LPequiv v1 v2 : Prop :=
       match v1, v2 with
         | VBool b1, VBool b2 => b1 = b2
         | VNat n1, VNat n2 => n1 = n2
         | VClos e1 t1, VClos e2 t2 =>
           list_forall2 atom_LPequiv e1 e2 /\ t1 = t2
         | VBool _, _ | VNat _, _ | VClos _ _, _ => False
       end.

Definition env_LPequiv : env -> env -> Prop :=
  list_forall2 atom_LPequiv.

Lemma atom_LPequiv_lab_inv :
  forall v1 v2 l1 l2,
    atom_LPequiv (Atom v1 l1) (Atom v2 l2) ->
    l1 = l2.
Proof.
  intros. inversion H; inversion H0; destruct_conjs; auto.
Qed.

Lemma atom_LPequiv_raise :
  forall v1 v2,
    atom_LPequiv (Atom v1 Bottom2) (Atom v2 Bottom2) ->
    atom_LPequiv (Atom v1 Top2) (Atom v2 Top2).
Proof.
  intros v1 v2 H. destruct L.
  - destruct v1; destruct v2; destruct H; destruct H; destruct_conjs;
        inversion H; try inversion H1; subst; auto.
    + destruct H2. left. auto.
    + right. right. auto.
    + destruct H2. left. auto.
    + right. right. auto.
    + left. auto.
    + right. right. auto.
  - destruct v1; destruct v2; destruct H; destruct H; destruct_conjs;
        inversion H; inversion H1; inversion H2; subst.
    + destruct H2. left. auto.
    + right. right. auto.
    + left. auto.
    + right. right. auto.
    + left. auto.
    + right. right.  auto.
Qed.

End IndistinguishabilityTwo.

Definition atom_Lequiv := fun L => atom_LPequiv L (fun _ _ => True).

Definition value_Lequiv := fun L => value_LPequiv L (fun _ _ => True).

Definition env_Lequiv := fun L => env_LPequiv L (fun _ _ => True).

Lemma atom_value_env_LPequiv_Lequiv :
  forall L P,
    (forall a1 a2,
       atom_LPequiv L P a1 a2 -> atom_Lequiv L a1 a2)
    /\ (forall v1 v2,
          value_LPequiv L P v1 v2 -> value_Lequiv L v1 v2)
    /\ (forall e1 e2,
          env_LPequiv L P e1 e2 -> env_Lequiv L e1 e2).
Proof.
  intros. apply atom_value_env_mutind.
  - intros v1 Hv l1 a2 H. destruct a2 as [v2 l2].
    destruct L; destruct l1; destruct l2.
    + assert (value_LPequiv Bottom2 P v1 v2) by
          (destruct H; destruct H; destruct_conjs; try inversion H1; auto).
      apply Hv in H0. right. left. auto.
    + apply atom_LPequiv_lab_inv in H. inversion H.
    + apply atom_LPequiv_lab_inv in H. inversion H.
    + destruct v1; destruct v2; left; repeat (split; auto).
      * assert (t0 = t /\ env_LPequiv Bottom2 P l l0) by
            (split; destruct H; destruct H; destruct_conjs; subst; auto).
        destruct_conjs; subst.
        assert (value_Lequiv Bottom2 (VClos l t) (VClos l0 t)) by
            (apply Hv; split; auto).
        assert (env_Lequiv Bottom2 l l0) by
            (destruct H0; destruct H; destruct_conjs; subst; auto).
        assumption.
      * destruct H; destruct H; destruct_conjs; subst; auto.
    + assert (value_LPequiv Top2 P v1 v2) by
          (destruct H; destruct H; destruct_conjs; try inversion H; auto).
      apply Hv in H0. right. right. auto.
    + apply atom_LPequiv_lab_inv in H. inversion H.
    + apply atom_LPequiv_lab_inv in H. inversion H.
    + assert (value_LPequiv Top2 P v1 v2) by
          (destruct H; destruct H; destruct_conjs; try inversion H; auto).
      apply Hv in H0. right. right. auto.
  - intros n1 v2 H. destruct v2; inversion H; reflexivity.
  - intros n1 v2 H. destruct v2; inversion H; reflexivity.
  - intros e1 He t1 v2 H. destruct v2 as [| | e2 t2].
    + inversion H.
    + inversion H.
    + assert (env_LPequiv L P e1 e2) by (destruct H; auto).
      assert (t2 = t1) by (destruct H; symmetry; assumption).
      apply He in H0. subst. split; auto.
  - intros e1.
    induction e1 as [| a1 e1']; intros Ha e2 H;
    destruct e2 as [| a2 e2']; inversion H; auto; split.
    + apply (Ha 0); auto.
    + apply IHe1'. intros. apply (Ha (S n)); auto. assumption.
Qed.

Lemma atom_LPequiv_Lequiv :
  forall L P a1 a2,
    atom_LPequiv L P a1 a2 -> atom_Lequiv L a1 a2.
Proof. apply atom_value_env_LPequiv_Lequiv. Qed.

Lemma value_LPequiv_Lequiv :
  forall L P v1 v2,
    value_LPequiv L P v1 v2 -> value_Lequiv L v1 v2.
Proof. apply atom_value_env_LPequiv_Lequiv. Qed.

Lemma env_LPequiv_Lequiv :
  forall L P e1 e2,
    env_LPequiv L P e1 e2 -> env_Lequiv L e1 e2.
Proof. apply atom_value_env_LPequiv_Lequiv. Qed.

Lemma atom_value_env_LPequiv_refl :
  forall L (P : value -> value -> Prop),
    (forall x, P x x) ->
    (forall a, atom_LPequiv L P a a) /\
    (forall v, value_LPequiv L P v v) /\
    (forall e, env_LPequiv L P e e).
Proof.
  intros L P Prefl. apply atom_value_env_mutind.
  - intros v Hv l.
    destruct v as [b | n | e t];
      (destruct L; destruct l; [
         right; left; auto |
         left; auto |
         right; right; auto |
         right; right; auto
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
  forall L (P : value -> value -> Prop),
    (forall x, P x x) ->
    (forall a, atom_LPequiv L P a a).
Proof.
  intros. apply atom_value_env_LPequiv_refl. auto.
Qed.

Lemma value_LPequiv_refl :
  forall L (P : value -> value -> Prop),
    (forall x, P x x) ->
    (forall v, value_LPequiv L P v v).
Proof.
  intros. apply atom_value_env_LPequiv_refl. auto.
Qed.

Lemma env_LPequiv_refl :
  forall L (P : value -> value -> Prop),
    (forall x, P x x) ->
    (forall e, env_LPequiv L P e e).
Proof.
  intros. apply atom_value_env_LPequiv_refl. auto.
Qed.


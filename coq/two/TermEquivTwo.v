Require Import LabelAlgebra.
Require Import LambdaTwo.

Set Implicit Arguments.

(** * Equivalence on terms: syntactic equality + equivalence on labels and authorities. *)
Section TermEquivTwo.

Fixpoint term_equiv (t1 t2 : term) {struct t1} : Prop :=
  match t1, t2 with
    | TNat n1, TNat n2 =>
      n1 = n2
    | TVar n1, TVar n2 =>
      n1 = n2
    | TLam t1, TLam t2 =>
      term_equiv t1 t2
    | TApp t1 t1', TApp t2 t2' =>
      term_equiv t1 t2 /\ term_equiv t1' t2'
    | TRelabel t1, TRelabel t2 =>
      term_equiv t1 t2
    | TNat _, _ | TVar _, _ | TLam _, _
    | TApp _ _, _ | TRelabel _, _ => False
  end.

Global Instance Equivalence_term_equiv : Equivalence term_equiv.
Proof.
constructor.
* intro t. induction t; try solve [simpl; auto].
* intros t1.
  induction t1; intros t2 H; destruct t2; simpl in *; try tauto; intuition auto.
* intro t1; induction t1; intros t2 t3 H12 H23; destruct t2; simpl in *;
  try tauto; destruct t3; simpl in *; try tauto; try congruence;
  intuition eauto; try solve [etransitivity; eassumption].
Qed.

End TermEquivTwo.

Hint Extern 1 =>
match goal with
  | |- term_equiv _ _ => reflexivity
end.

(** * Equivalent atoms, values and environments. *)
Section Atoms.

Fixpoint atom_equiv (a1 a2 : atom) {struct a1} : Prop :=
  match a1, a2 with
    | Atom v1 l1, Atom v2 l2 =>
      value_equiv v1 v2 /\ l1 =L l2
  end
with value_equiv (v1 v2 : value) {struct v1} : Prop :=
       match v1, v2 with
         | VNat n1, VNat n2 => n1 = n2
         | VClos e1 t1, VClos e2 t2 =>
           list_forall2 atom_equiv e1 e2
           /\ term_equiv t1 t2
         | VNat _, _ | VClos _ _, _ => False
       end.

Definition env_equiv := list_forall2 atom_equiv.

Lemma atom_value_env_equiv_refl :
  (forall a, atom_equiv a a)
  /\ (forall v, value_equiv v v)
  /\ (forall e, env_equiv e e).
Proof.
  apply atom_value_env_mutind; intros; simpl; auto.
  induction l; simpl; auto.
  induction l.
    reflexivity.
    simpl. split.
      apply (H 0 a). reflexivity.
      apply IHl. intros n b Hb. apply (H (S n) b). assumption.
Qed.

Lemma atom_value_env_equiv_sym :
  (forall a1 a2, atom_equiv a1 a2 -> atom_equiv a2 a1)
  /\ (forall v1 v2, value_equiv v1 v2 -> value_equiv v2 v1)
  /\ (forall e1 e2, env_equiv e1 e2 -> env_equiv e2 e1).
Proof.
apply atom_value_env_mutind; intros; simpl in *.
* destruct a2. simpl. intuition auto.
* destruct v2; simpl; auto.
* destruct v2; simpl; intuition auto.
  apply H. assumption.
  symmetry. assumption.
* generalize dependent e2.
  induction l; intros e2 He; destruct e2; simpl in *; try tauto.
  split.
  - apply (H 0 a). reflexivity. tauto.
  - apply IHl. intros n b Hb. apply (H (S n) b). assumption. tauto.
Qed.

Lemma atom_value_env_equiv_trans :
  (forall a1 a2 a3,
     atom_equiv a1 a2 -> atom_equiv a2 a3 -> atom_equiv a1 a3)
  /\ (forall v1 v2 v3,
        value_equiv v1 v2 -> value_equiv v2 v3 -> value_equiv v1 v3)
  /\ (forall e1 e2 e3,
        env_equiv e1 e2 -> env_equiv e2 e3 -> env_equiv e1 e3).
Proof.
apply atom_value_env_mutind; intros; simpl in *.
* destruct a2. simpl in *. destruct a3. intuition.
  eauto. etransitivity; eassumption. etransitivity; eassumption.
* destruct v2; simpl in *; destruct v3; eauto.
* destruct v2; simpl in *; destruct v3; intuition auto.
  eapply H; eassumption.
  etransitivity; eassumption.
* generalize dependent e3. generalize dependent e2.
  induction l; intros e2 H12 e3 H23; destruct e2; simpl in *;
  destruct e3; try tauto.
  split.
  - apply (H 0 a eq_refl a0); tauto.
  - apply IHl with (e2 := e2); try tauto.
    intros n b Hb. apply (H (S n) b). assumption.
Qed.

Global Instance Equivalence_atom_equiv : Equivalence atom_equiv.
Proof.
constructor.
* destruct atom_value_env_equiv_refl as [? _]. assumption.
* destruct atom_value_env_equiv_sym as [? _]. assumption.
* destruct atom_value_env_equiv_trans as [? _]. assumption.
Qed.

Global Instance Equivalence_value_equiv : Equivalence value_equiv.
Proof.
constructor.
* destruct atom_value_env_equiv_refl as [_ [? _]]. assumption.
* destruct atom_value_env_equiv_sym as [_ [? _]]. assumption.
* destruct atom_value_env_equiv_trans as [_ [? _]]. assumption.
Qed.

Global Instance Equivalence_env_equiv : Equivalence env_equiv.
Proof.
constructor.
* destruct atom_value_env_equiv_refl as [_ [_ ?]]. assumption.
* destruct atom_value_env_equiv_sym as [_ [_ ?]]. assumption.
* destruct atom_value_env_equiv_trans as [_ [_ ?]]. assumption.
Qed.

End Atoms.

Hint Unfold atom_equiv value_equiv env_equiv.

Hint Extern 1 =>
match goal with
| |- atom_equiv _ _ => reflexivity
| |- value_equiv _ _ => reflexivity
| |- env_equiv _ _ => reflexivity
end.

Section EquivEq.

Lemma term_equiv_eq :
  forall t1 t2,
    term_equiv t1 t2 <-> t1 = t2.
Proof.
  split; generalize dependent t2.
  induction t1; intros; destruct t2; simpl in H; auto;
    try (apply IHt1 in H; subst; reflexivity).
    destruct H. apply IHt1_1 in H. apply IHt1_2 in H0. subst. reflexivity.
  induction t1; intros; destruct t2; rewrite H; inversion H; try reflexivity;
    subst; simpl; auto.
Qed.

Lemma atom_value_env_equiv_eq :
  (forall a1 a2, atom_equiv a1 a2 <-> a1 = a2)
  /\ (forall v1 v2, value_equiv v1 v2 <-> v1 = v2)
  /\ (forall e1 e2, env_equiv e1 e2 <-> e1 = e2).
Proof.
  apply atom_value_env_mutind.
  intros v1 Hv. split; rename l into l1; intros H;
    destruct v1 as [n1 | e1 t1]; destruct l1; destruct a2 as [v2 l2];
      destruct v2; destruct l2; destruct H; auto;
      apply Hv in H; rewrite H; reflexivity.
  intros n1. split; intros H; destruct v2; try rewrite H; auto.
  intros e1 He t1. split; intros H;
    destruct v2; destruct H; try apply term_equiv_eq in H0; try apply He in H;
      subst; auto.
  intros e1.
    induction e1 as [| a1 e1']; intros Ha e2; split; intros H;
      destruct e2 as [| a2 e2']; inversion H; auto.
    apply (Ha 0 a1) in H0.
    apply IHe1' in H1. subst. reflexivity.
      split; intros; subst; auto.
        assert (atIndex (a2 :: e1') (S n) = Some a) by auto.
          apply (Ha (S n) a). assumption. assumption.
    reflexivity.
Qed.

Lemma atom_equiv_eq :
  forall a1 a2,
    atom_equiv a1 a2 <-> a1 = a2.
Proof. apply atom_value_env_equiv_eq. Qed.

Lemma value_equiv_eq :
  forall v1 v2,
    value_equiv v1 v2 <-> v1 = v2.
Proof. apply atom_value_env_equiv_eq. Qed.

Lemma env_equiv_eq :
  forall e1 e2,
    atom_equiv e1 e2 <-> e1 = e2.
Proof. apply atom_value_env_equiv_eq. Qed.
  
End EquivEq.

(** * Compatibility of evaluation with respect to equivalence. *)
Section Eval.

Lemma eval_equiv_compat (pc1 pc2 : two) (e1 e2 : env)
      (t1 t2 : term) (a1 a2 : atom) :
  pc1 =L pc2 ->
  env_equiv e1 e2 ->
  term_equiv t1 t2 ->
  pc1; e1 ⊢ t1 ⇓ a1 ->
  pc2; e2 ⊢ t2 ⇓ a2 ->
  atom_equiv a1 a2.
Proof.
intros Hpc He Ht Heval Heval'.
generalize dependent a2.
generalize dependent t2.
generalize dependent e2.
generalize dependent pc2.
induction Heval; intros pc' Hpc e' He t' Ht a' Heval';
destruct t'; simpl in Ht; try tauto; inversion Heval'; subst;
try solve [simpl; auto].
* assert (atom_equiv (Atom v l) (Atom v0 l0)) as [Hv Hl].
  + eapply list_forall2_atIndex; eauto.
  + split.
    - assumption.
    - rewrite Hl. rewrite Hpc. reflexivity.
* destruct Ht as [Ht1 Ht2].
  specialize (IHHeval1 _ Hpc _ He _ Ht1 _ H1).
  destruct IHHeval1 as [[He1' Ht1'] Hpc1].
  specialize (IHHeval2 _ Hpc _ He _ Ht2 _ H4).
  apply IHHeval3 with (pc2 := l0) (e2 := a0 :: e1'0) (t2 := t1'0); auto.
  split; auto.
Qed.

Lemma eval_equiv_compat_fun (pc1 pc2 : two) (e1 e2 : env)
      (t1 t2 : term) (a1 : atom) :
  pc1 =L pc2 ->
  env_equiv e1 e2 ->
  term_equiv t1 t2 ->
  pc1; e1 ⊢ t1 ⇓ a1 ->
  exists a2,
    pc2; e2 ⊢ t2 ⇓ a2 /\ atom_equiv a1 a2.
Proof.
intros Hpc He Ht Heval.
generalize dependent t2.
generalize dependent e2.
generalize dependent pc2.
induction Heval; intros pc' Hpc e' He t' Ht;
destruct t'; simpl in Ht; try tauto.
* subst n0. exists (Atom (VNat n) pc'). auto.
* subst n0.
  destruct (list_forall2_atIndex_fun _ _ _ _ _ He H) as [a' [na' Ha']].
  destruct a' as [v' l']. destruct Ha' as [Hv' Hl'].
  exists (Atom v' (l' ⊔ pc')). split; auto. split; auto.
  rewrite Hl'. rewrite Hpc. reflexivity.
* exists (Atom (VClos e' t') pc'). auto.
* destruct Ht as [Ht1 Ht2].
  specialize (IHHeval1 _ Hpc _ He _ Ht1).
  destruct IHHeval1 as [[v1' l1'] [Heval1' [Hv1' Hl1']]].
  destruct v1'; simpl in Hv1'; try tauto.
  rename l into e1''. rename t into t1''.
  destruct Hv1' as [He1'' Ht1''].
  specialize (IHHeval2 _ Hpc _ He _ Ht2).
  destruct IHHeval2 as [a2' [Heval2' Ha2']].
  specialize (IHHeval3 _ Hl1' (a2' :: e1'') (conj Ha2' He1'') _ Ht1'').
  destruct IHHeval3 as [a3' [Heval3' Ha3']].
  exists a3'. eauto.
Qed.

Lemma eval_nil_change_pc (pc1 pc2 : two) (t : term) (a : atom) :
  pc1 =L pc2 ->
  pc1; nil ⊢ t ⇓ a ->
  exists a',
    pc2; nil ⊢ t ⇓ a' /\ atom_equiv a a'.
Proof.
intros Hpc Heval.
apply @eval_equiv_compat_fun with (pc1 := pc1) (e1 := nil) (t1 := t); auto.
Qed.

End Eval.

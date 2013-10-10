Require Import LabelAlgebra.
Require Import Lambda.

Set Implicit Arguments.

(** * Equivalence on terms: syntactic equality + equivalence on labels and authorities. *)
Section TermEquiv.

Context {A L: Type} {LA: LabelAlgebra A L}.

Fixpoint term_equiv (t1 t2: term A L) {struct t1} : Prop :=
match t1, t2 with
| TBool b1, TBool b2 =>
    b1 = b2
| TVar n1, TVar n2 =>
    n1 = n2
| TLam t1, TLam t2 =>
    term_equiv t1 t2
| TApp t1 t1', TApp t2 t2' =>
    term_equiv t1 t2 /\ term_equiv t1' t2'
| TRelabel t1 a1 l1, TRelabel t2 a2 l2 =>
    term_equiv t1 t2 /\ a1 =A a2 /\ l1 =L l2
| TBool _, _ | TVar _, _ | TLam _, _
| TApp _ _, _ | TRelabel _ _ _, _ => False
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

End TermEquiv.

Hint Extern 1 =>
match goal with
| |- term_equiv _ _ => reflexivity
end.

(** * Preservation and reflection of term equivalence by application of maps. *)
Section Maps.

Context {A1 L1 A2 L2}
        (LA1: LabelAlgebra A1 L1)
        (LA2: LabelAlgebra A2 L2)
        (m: LA1 ==> LA2).

Lemma term_equiv_preserved_sufficient :
  (forall l1 l2 : L1, l1 =L l2 -> Lmap m l1 =L Lmap m l2) ->
  (forall a1 a2 : A1, a1 =A a2 -> Amap m a1 =A Amap m a2) ->
  forall t1 t2,
    term_equiv t1 t2 ->
    term_equiv (apply m t1) (apply m t2).
Proof.
intros HL HA t1.
induction t1; intros t2 H; destruct t2;
try solve [simpl in H; try tauto; simpl; intuition auto].
* destruct H as [? [? ?]]. split; auto.
Qed.

Lemma term_equiv_reflected_sufficient :
  (forall l1 l2 : L1, Lmap m l1 =L Lmap m l2 -> l1 =L l2) ->
  (forall a1 a2 : A1, Amap m a1 =A Amap m a2 -> a1 =A a2) ->
  forall t1 t2,
    term_equiv (apply m t1) (apply m t2) ->
    term_equiv t1 t2.
Proof.
intros HL HA t1.
induction t1; intros t2 H; destruct t2;
try solve [simpl in H; try tauto; simpl; intuition auto].
* destruct H as [? [? ?]]. split; auto.
Qed.

End Maps.

(** * Equivalent atoms, values and environments. *)
Section Atoms.

Context {A L: Type} {LA: LabelAlgebra A L}.

Fixpoint atom_equiv (a1 a2: atom A L) {struct a1} : Prop :=
match a1, a2 with
| Atom v1 l1, Atom v2 l2 =>
  value_equiv v1 v2 /\ l1 =L l2
end
with value_equiv (v1 v2: value A L) {struct v1} : Prop :=
match v1, v2 with
| VBool b1, VBool b2 => b1 = b2
| VClos e1 t1, VClos e2 t2 =>
  list_forall2 atom_equiv e1 e2
  /\ term_equiv t1 t2
| VBool _, _ | VClos _ _, _ => False
end.

Definition env_equiv := list_forall2 atom_equiv.

Lemma atom_value_env_equiv_refl :
  (forall a, atom_equiv a a)
  /\ (forall v, value_equiv v v)
  /\ (forall e, env_equiv e e).
Proof.
apply atom_value_env_mutind; intros; simpl; auto.
induction l; simpl; auto. split.
- apply (H 0 a). reflexivity.
- apply IHl. intros n b Hb. apply (H (S n) b). assumption.
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

(** * Compatibility of evaluation with respect to equivalence. *)
Section Eval.

Context {A L: Type} {LA: LabelAlgebra A L}.

Lemma eval_equiv_compat (pc1 pc2: L) (e1 e2: env A L)
      (t1 t2: term A L) (a1 a2: atom A L) :
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
* destruct Ht as [Ht [Ha Hl]].
  specialize (IHHeval _ Hpc _ He _ Ht _ H6).
  destruct IHHeval as [Hv' Hl']. split; auto.
Qed.

Lemma eval_equiv_compat_fun (pc1 pc2: L) (e1 e2: env A L)
      (t1 t2: term A L) (a1: atom A L) :
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
* subst b0. exists (Atom (VBool b) pc'). auto.
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
* destruct Ht as [Ht [Ha Hl]].
  specialize (IHHeval _ Hpc _ He _ Ht).
  destruct IHHeval as [[v'' l''] [Heval'' [Hv'' Hl'']]].
  exists (Atom v'' l0). split.
  + econstructor. eassumption.
    transitivity l1; auto.
    transitivity l; auto.
    intuition. eauto.
  + auto.
Qed.

Lemma eval_nil_change_pc (pc1 pc2: L) (t: term A L) (a: atom A L) :
  pc1 =L pc2 ->
  pc1; nil ⊢ t ⇓ a ->
  exists a',
    pc2; nil ⊢ t ⇓ a' /\ atom_equiv a a'.
Proof.
intros Hpc Heval.
apply @eval_equiv_compat_fun with (pc1 := pc1) (e1 := nil) (t1 := t); auto.
Qed.

End Eval.

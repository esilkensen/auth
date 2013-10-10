Require Import MyTactics.
Require Import LabelAlgebra.
Require Import Lambda.
Require Import Auth.
Require Import TermEquiv.

Set Implicit Arguments.

(** * Indistinguishable booleans. *)
Section BooleanIndistinguishability.

Context {A L: Type} {LA: LabelAlgebra A L} (a: A) (l: L).

Definition bool_Lequiv (a1 a2: atom A L) : Prop :=
match a1, a2 with
| Atom (VBool b1) l1, Atom (VBool b2) l2 =>
  (l1 ⊑[a] l \/ l2 ⊑[a] l) -> (b1 = b2 /\ l1 =L l2)
| _, _ => False
end.

Definition bool_env_Lequiv := list_forall2 bool_Lequiv.

(** * Boolean indistinguishability is symmetric and transitive. *)
Global Instance Symmetric_bool_Lequiv : Symmetric bool_Lequiv.
Proof.
intros [v1 l1] [v2 l2] H. simpl in *.
destruct v1; destruct v2; try tauto.
intuition.
Qed.

Global Instance Transitive_bool_Lequiv : Transitive bool_Lequiv.
Proof.
intros [v1 l1] [v2 l2] [v3 l3] H12 H23. simpl in *.
destruct v1; destruct v2; destruct v3; try tauto.
intros [H | H].
* destruct H12 as [? [? ?]]; auto.
  destruct H23 as [? [? ?]]. left. transitivity l1; auto.
  splits. congruence. transitivity l2; auto. transitivity l2; auto.
* destruct H23 as [? [? ?]]; auto.
  destruct H12 as [? [? ?]]. right. transitivity l3; auto.
  splits. congruence. transitivity l2; auto. transitivity l2; auto.
Qed.

Global Instance Symmetric_bool_env_Lequiv : Symmetric bool_env_Lequiv.
Proof.
intros e1 e2. apply list_forall2_sym.
apply Symmetric_bool_Lequiv.
Qed.

Global Instance Transitive_bool_env_Lequiv : Transitive bool_env_Lequiv.
Proof.
intros e1 e2 e3. apply list_forall2_trans.
apply Transitive_bool_Lequiv.
Qed.

(** * Indistinguishable booleans have no authority. *)
Lemma bool_Lequiv_auth_bottom_left (a1 a2: atom A L) :
  bool_Lequiv a1 a2 ->
  atom_auth a1 =A bottom.
Proof.
intro H. destruct a1 as [v1 l1]. destruct a2 as [v2 l2].
simpl in H. destruct v1; destruct v2; try tauto. reflexivity.
Qed.

Lemma bool_Lequiv_auth_bottom_right (a1 a2: atom A L) :
  bool_Lequiv a1 a2 ->
  atom_auth a2 =A bottom.
Proof.
intro H. symmetry in H.
eauto using bool_Lequiv_auth_bottom_left.
Qed.

Lemma env_bool_Lequiv_auth_bottom_left (e1 e2: env A L) :
  bool_env_Lequiv e1 e2 ->
  env_auth e1 =A bottom.
Proof.
revert e2. induction e1; intros e2 H; auto.
destruct e2; simpl in H; destruct H. simpl.
apply bool_Lequiv_auth_bottom_left in H.
rewrite H. rewrite (IHe1 e2); auto.
Qed.

Lemma env_bool_Lequiv_auth_bottom_right (e1 e2: env A L) :
  bool_env_Lequiv e1 e2 ->
  env_auth e2 =A bottom.
Proof.
intro H. symmetry in H.
eauto using env_bool_Lequiv_auth_bottom_left.
Qed.

End BooleanIndistinguishability.

(** * Monotonicity properties of boolean indistinguishability. *)
Section Monotonicity.

Context {A L: Type} {LA: LabelAlgebra A L}.

Lemma bool_Lequiv_auth_antimonotone :
  forall (auth auth': A) (lab: L) a1 a2,
    auth ≤ auth' ->
    bool_Lequiv auth' lab a1 a2 ->
    bool_Lequiv auth  lab a1 a2.
Proof.
intros auth auth' lab [v1 l1] [v2 l2] Hleq H.
simpl in *; destruct v1; destruct v2; try tauto.
intro Hlab.
assert (l1 ⊑[auth']lab \/ l2 ⊑[auth']lab) as Hlab'.
{ destruct Hlab; eauto. }
specialize (H Hlab'). destruct H; split; eauto.
Qed.

Lemma bool_Lequiv_label_antimonotone :
  forall (auth: A) (lab lab': L) a1 a2,
    lab ⊑[auth] lab' ->
    bool_Lequiv auth lab' a1 a2 ->
    bool_Lequiv auth lab  a1 a2.
Proof.
intros auth lab lab' [v1 l1] [v2 l2] Hleq H.
simpl in *; destruct v1; destruct v2; try tauto.
intro Hlab.
assert (l1 ⊑[auth]lab' \/ l2 ⊑[auth]lab') as Hlab'.
{ destruct Hlab; [left | right]; transitivity lab; assumption. }
specialize (H Hlab'). destruct H; split; eauto.
Qed.

Lemma bool_env_Lequiv_auth_antimonotone :
  forall (auth auth': A) (lab: L) e1 e2,
    auth ≤ auth' ->
    bool_env_Lequiv auth' lab e1 e2 ->
    bool_env_Lequiv auth  lab e1 e2.
Proof.
intros auth auth' lab e1.
induction e1; intros e2 Hleq H; destruct e2; simpl in *; auto.
destruct H. eauto using bool_Lequiv_auth_antimonotone.
Qed.

Lemma bool_env_Lequiv_label_antimonotone :
  forall (auth: A) (lab lab': L) e1 e2,
    lab ⊑[auth] lab' ->
    bool_env_Lequiv auth lab' e1 e2 ->
    bool_env_Lequiv auth lab  e1 e2.
Proof.
intros auth auth' lab e1.
induction e1; intros e2 Hleq H; destruct e2; simpl in *; auto.
destruct H. eauto using bool_Lequiv_label_antimonotone.
Qed.

End Monotonicity.

(** * Invariance under injections. *)

Lemma bool_Lequiv_injection {A1 L1 A2 L2: Type}
      {LA1: LabelAlgebra A1 L1} {LA2: LabelAlgebra A2 L2}
      (m: LA1 ==> LA2) :
  LAinjection m ->
  forall a l x1 x2,
    bool_Lequiv a l x1 x2 <->
    bool_Lequiv (Amap m a) (Lmap m l) (apply m x1) (apply m x2).
Proof.
intros [[HAcompat [HAbottom [HAjoin [HLcompat [HLdef [HLjoin [HLmeet Hmon]]]]]]]
          [[HAinj HLinj] HflowsTo]] a l [v1 l1] [v2 l2].
pose proof (sufficient_monotone m HAbottom Hmon) as HLmon.
pose proof (sufficient_antitone m HAbottom HflowsTo) as HLanti.
destruct v1; destruct v2; simpl; try tauto.
split; intro H.
* intros [Hlab | Hlab]; apply HflowsTo in Hlab; destruct H as [? [? ?]]; auto.
* intros [Hlab | Hlab]; apply Hmon in Hlab; destruct H as [? [? ?]]; auto.
Qed.

(** * Compatibility with equivalence. *)
Section Compatibility.

Context {A L: Type} {LA: LabelAlgebra A L}
        (auth: A) (lab: L).

Lemma bool_Lequiv_equiv_r :
  forall (a1 a2 a3: atom A L),
    bool_Lequiv auth lab a1 a2 ->
    atom_equiv a2 a3 ->
    bool_Lequiv auth lab a2 a3.
Proof.
intros a1 a2 a3 H12 H23.
destruct a1 as [v1 l1]; destruct a2 as [v2 l2]; destruct a3 as [v3 l3].
destruct v1; try solve [simpl in H12; tauto].
destruct v2; try solve [compute in H12; tauto].
destruct v3; try solve [compute in H23; tauto].
destruct H23 as [? ?].
intro Hlab.
assert (l1 ⊑[ auth]lab \/ l2 ⊑[ auth]lab) as Hlab'.
{ destruct Hlab; right; auto. transitivity l3; auto. }
specialize (H12 Hlab'). destruct H12; split; eauto.
Qed.

Lemma bool_Lequiv_equiv_l :
  forall (a1 a2 a3: atom A L),
    atom_equiv a1 a2 ->
    bool_Lequiv auth lab a2 a3 ->
    bool_Lequiv auth lab a1 a2.
Proof.
intros a1 a2 a3 H12 H23.
symmetry in H12. symmetry in H23. symmetry.
eapply bool_Lequiv_equiv_r; eassumption.
Qed.

End Compatibility.

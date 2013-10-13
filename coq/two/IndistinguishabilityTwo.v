Require Import Program.Tactics.
Require Import MyTactics.
Require Import LabelAlgebra.
Require Import LambdaTwo.
Require Import TermEquivTwo.

(** * Indistinguishability relations. *) 
Section IndistinguishabilityTwo.

Context (l : two)
        (P : value -> value -> Prop)
        (Prefl : forall x, P x x)
        (Psym : forall x y, P x y -> P y x)
        (Ptrans : forall x y z, P x y -> P y z -> P x z).

Fixpoint atom_Lequiv a1 a2 : Prop :=
  match a1, a2 with
    | Atom v1 l1, Atom v2 l2 =>
      (l = Bottom2 /\ l1 = l2 /\ l1 = Top2 /\ P v1 v2) \/
      (l = Bottom2 /\ l1 = l2 /\ l1 = Bottom2 /\ value_Lequiv v1 v2) \/
      (l = Top2 /\ l1 = l2 /\ value_Lequiv v1 v2)
  end
with value_Lequiv v1 v2 : Prop :=
       match v1, v2 with
         | VNat n1, VNat n2 => n1 = n2
         | VClos e1 t1, VClos e2 t2 =>
           list_forall2 atom_Lequiv e1 e2 /\ term_equiv t1 t2
         | VNat _, _ | VClos _ _, _ => False
       end.

Definition env_Lequiv : env -> env -> Prop :=
  list_forall2 atom_Lequiv.

(** ** The indistinguishability relations are equivalences. *)
Lemma atom_value_env_Lequiv_refl :
  (forall a, atom_Lequiv a a)
  /\ (forall v, value_Lequiv v v)
  /\ (forall e, env_Lequiv e e).
Proof.
  apply atom_value_env_mutind; intros; simpl; auto.
  destruct l; destruct l0; auto. right. auto.
  induction l0.
    reflexivity.
    simpl. split.
      apply (H 0 a). reflexivity.
      apply IHl0. intros n b Hb. apply (H (S n) b). assumption.
Qed.

Lemma atom_value_env_Lequiv_sym :
  (forall a1 a2, atom_Lequiv a1 a2 -> atom_Lequiv a2 a1)
  /\ (forall v1 v2, value_Lequiv v1 v2 -> value_Lequiv v2 v1)
  /\ (forall e1 e2, env_Lequiv e1 e2 -> env_Lequiv e2 e1).
Proof.
  apply atom_value_env_mutind; intros. 
  destruct a2. simpl. simpl in H0.
  destruct H0; destruct H0; destruct_conjs; destruct l; subst; inversion H0.
    left. auto.
    right. left. auto.
    right. right. auto.
  destruct v2; inversion H. reflexivity.
  destruct v2. 
    destruct l0; simpl in H0; inversion H0.
    destruct l0.
      destruct l1.
        inversion H0. simpl. split. reflexivity. symmetry. assumption.
        simpl in H0. inversion H0. inversion H1.
      simpl. split. apply H.
        destruct l1; inversion H0; inversion H1; auto.
        inversion H0. symmetry. assumption.
  generalize dependent e2.
  induction l0; intros e2 H2; destruct e2; simpl in *; try tauto.
  split. apply (H 0). reflexivity. inversion H2. assumption.
  apply IHl0. intros n b Hb. apply (H (S n) b). assumption. tauto.
Qed.

Lemma atom_value_env_Lequiv_trans :
  (forall a1 a2 a3,
     atom_Lequiv a1 a2 -> atom_Lequiv a2 a3 -> atom_Lequiv a1 a3)
  /\ (forall v1 v2 v3,
        value_Lequiv v1 v2 -> value_Lequiv v2 v3 -> value_Lequiv v1 v3)
  /\ (forall e1 e2 e3,
        env_Lequiv e1 e2 -> env_Lequiv e2 e3 -> env_Lequiv e1 e3).
Proof.
  apply atom_value_env_mutind; intros.
  destruct a2. destruct a3. simpl in *.
  destruct H0; destruct H0; destruct H1; destruct H1;
  destruct_conjs; subst; destruct l; destruct t0; try clear_dup; inversion H0;
  try inversion H1; try inversion H2; try inversion H3; try inversion H4.
    apply (Ptrans v v0 v1) in H7. left. auto. assumption.
    apply (H v0 v1) in H4. right. left. auto. assumption.
    apply (H v0 v1) in H3. right. right. auto. assumption.
    apply (H v0 v1) in H3. right. right. auto. assumption.
    destruct v2; destruct v3; simpl in *; auto.
    destruct v2; destruct v3; simpl in *; auto.
      unfold env_Lequiv in H.
      destruct H0. destruct H1. split.
        apply (H l1 l2). assumption. assumption.
        transitivity t0; assumption.
    generalize dependent e3. generalize dependent e2.
    induction l0; intros e2 H12 e3 H23; destruct e2; simpl in *;
    destruct e3; try tauto. destruct H12. destruct H23.
    split.
      apply H with (n:=0) (a2:=a0); tauto.
      apply IHl0 with (e2:=e2); try tauto.
        intros n b Hb. apply (H (S n) b). assumption.
Qed.
    
Global Instance Equivalence_atom_Lequiv : Equivalence atom_Lequiv.
Proof.
constructor.
* destruct atom_value_env_Lequiv_refl as [? _]. assumption.
* destruct atom_value_env_Lequiv_sym as [? _]. assumption.
* destruct atom_value_env_Lequiv_trans as [? _]. assumption.
Qed.

Global Instance Equivalence_value_Lequiv : Equivalence value_Lequiv.
Proof.
constructor.
* destruct atom_value_env_Lequiv_refl as [_ [? _]]. assumption.
* destruct atom_value_env_Lequiv_sym as [_ [? _]]. assumption.
* destruct atom_value_env_Lequiv_trans as [_ [? _]]. assumption.
Qed.

Global Instance Equivalence_env_Lequiv : Equivalence env_Lequiv.
Proof.
constructor.
* destruct atom_value_env_Lequiv_refl as [_ [_ ?]]. assumption.
* destruct atom_value_env_Lequiv_sym as [_ [_ ?]]. assumption.
* destruct atom_value_env_Lequiv_trans as [_ [_ ?]]. assumption.
Qed.

End IndistinguishabilityTwo.

(** * Monotonicity properties of indistinguishability. *)
Section Monotonicity.

Context {A L: Type} {LA: LabelAlgebra A L}.

(** ** With respect to authorities. *)
Check atom_Lequiv.
Lemma Lequiv_auth_antimonotone :
  forall (auth auth': A) (lab: L),
    auth ≤ auth' ->
    (forall a1 a2,  atom_Lequiv auth' lab a1 a2 -> atom_Lequiv auth lab a1 a2)
    /\ (forall v1 v2, value_Lequiv auth' lab v1 v2 -> value_Lequiv auth lab v1 v2)
    /\ (forall e1 e2, env_Lequiv auth' lab e1 e2 -> env_Lequiv auth lab e1 e2).
Proof.
intros auth auth' lab Hleq.
apply atom_value_env_mutind; intros; simpl; auto.
* destruct a2; simpl in *. intro Hlab.
  fold (value_Lequiv auth lab v v0).
  assert (l ⊑[auth']lab \/ l0 ⊑[auth']lab) as Hlab'.
  { destruct Hlab; eauto. }
  specialize (H0 Hlab'). fold (value_Lequiv auth' lab v v0) in H0.
  destruct H0; split; eauto.
* destruct v2; simpl in *; destruct H0.
  fold (atom_Lequiv auth' lab) in H0. fold (env_Lequiv auth' lab) in H0.
  split; auto.
  fold (atom_Lequiv auth lab). fold (env_Lequiv auth lab). eauto.
* generalize dependent e2.
  induction l; intros e2 He2; simpl; auto. destruct e2; destruct He2. split.
  - apply (H 0 a). reflexivity. assumption.
  - apply IHl. intros n b Hb. apply (H (S n) b). assumption. assumption.
Qed.

Lemma atom_Lequiv_auth_antimonotone :
  forall (auth auth': A) (lab: L) (a1 a2: atom A L),
    auth ≤ auth' ->
    atom_Lequiv auth' lab a1 a2 ->
    atom_Lequiv auth  lab a1 a2.
Proof.
intros auth auth' lab a1 a2 Hleq.
destruct (Lequiv_auth_antimonotone auth auth' lab Hleq) as [? _].
auto.
Qed.

Lemma value_Lequiv_auth_antimonotone :
  forall (auth auth': A) (lab: L) (v1 v2: value A L),
    auth ≤ auth' ->
    value_Lequiv auth' lab v1 v2 ->
    value_Lequiv auth  lab v1 v2.
Proof.
intros auth auth' lab a1 a2 Hleq.
destruct (Lequiv_auth_antimonotone auth auth' lab Hleq) as [_ [? _]].
auto.
Qed.

Lemma env_Lequiv_auth_antimonotone :
  forall (auth auth': A) (lab: L) (e1 e2: env A L),
    auth ≤ auth' ->
    env_Lequiv auth' lab e1 e2 ->
    env_Lequiv auth  lab e1 e2.
Proof.
intros auth auth' lab a1 a2 Hleq.
destruct (Lequiv_auth_antimonotone auth auth' lab Hleq) as [_ [_ ?]].
auto.
Qed.

(** ** With respect to labels. *)
Lemma Lequiv_label_antimonotone :
  forall (auth: A) (lab lab': L),
    lab ⊑[auth] lab' ->
    (forall a1 a2,  atom_Lequiv auth lab' a1 a2 -> atom_Lequiv auth lab a1 a2)
    /\ (forall v1 v2, value_Lequiv auth lab' v1 v2 -> value_Lequiv auth lab v1 v2)
    /\ (forall e1 e2, env_Lequiv auth lab' e1 e2 -> env_Lequiv auth lab e1 e2).
Proof.
intros auth lab lab' Hleq.
apply atom_value_env_mutind; intros; simpl; auto.
* destruct a2; simpl in *. intro Hlab.
  fold (value_Lequiv auth lab v v0).
  assert (l ⊑[auth]lab' \/ l0 ⊑[auth]lab') as Hlab'.
  { destruct Hlab; [left | right]; transitivity lab; assumption. }
  specialize (H0 Hlab'). fold (value_Lequiv auth lab' v v0) in H0.
  destruct H0; split; eauto.
* destruct v2; simpl in *; destruct H0.
  fold (atom_Lequiv auth lab') in H0. fold (env_Lequiv auth lab') in H0.
  split; auto.
  fold (atom_Lequiv auth lab). fold (env_Lequiv auth lab). eauto.
* generalize dependent e2.
  induction l; intros e2 He2; simpl; auto. destruct e2; destruct He2. split.
  - apply (H 0 a). reflexivity. assumption.
  - apply IHl. intros n b Hb. apply (H (S n) b). assumption. assumption.
Qed.

Lemma atom_Lequiv_label_antimonotone :
  forall (auth: A) (lab lab': L) (a1 a2: atom A L),
    lab ⊑[auth] lab' ->
    atom_Lequiv auth lab' a1 a2 ->
    atom_Lequiv auth lab  a1 a2.
Proof.
intros auth lab lab' a1 a2 Hleq.
destruct (Lequiv_label_antimonotone auth lab lab' Hleq) as [? _].
auto.
Qed.

Lemma value_Lequiv_label_antimonotone :
  forall (auth: A) (lab lab': L) (v1 v2: value A L),
    lab ⊑[auth] lab' ->
    value_Lequiv auth lab' v1 v2 ->
    value_Lequiv auth lab  v1 v2.
Proof.
intros auth lab lab' v1 v2 Hleq.
destruct (Lequiv_label_antimonotone auth lab lab' Hleq) as [_ [? _]].
auto.
Qed.

Lemma env_Lequiv_label_antimonotone :
  forall (auth: A) (lab lab': L) (e1 e2: env A L),
    lab ⊑[auth] lab' ->
    env_Lequiv auth lab' e1 e2 ->
    env_Lequiv auth lab  e1 e2.
Proof.
intros auth lab lab' e1 e2 Hleq.
destruct (Lequiv_label_antimonotone auth lab lab' Hleq) as [_ [_ ?]].
auto.
Qed.

End Monotonicity.

(** * Compatibility with equivalence. *)
Section Compatibility.

Context {A L: Type} {LA: LabelAlgebra A L} (auth: A) (lab: L).

Notation value_pred := (value A L -> value A L -> Prop).

Context {P: value_pred}.

Lemma equiv_Lequiv_strong :
  (forall a1 a2,
     atom_equiv a1 a2 ->
     atom_Lequiv auth lab a1 a2)
  /\ (forall v1 v2,
        value_equiv v1 v2 ->
        value_Lequiv auth lab v1 v2)
  /\ (forall e1 e2,
        env_equiv e1 e2 ->
        env_Lequiv auth lab e1 e2).
Proof.
apply atom_value_env_mutind; intros; auto.
* destruct a2 as [v2 l2].
  destruct H0 as [Hv Hl]. fold value_equiv in Hv.
  intro Hlab. fold (value_Lequiv auth lab).
  auto.
* destruct v2; simpl in H0; try tauto.
  destruct H0 as [Henv Ht]. fold atom_equiv in Henv. fold env_equiv in Henv.
  split; auto.
  fold (atom_Lequiv auth lab). fold (env_Lequiv auth lab). auto.
* generalize dependent e2.
  induction l; intros l' Henv; destruct l'; simpl in Henv; auto.
  destruct Henv. split.
  + apply (H 0 a); auto.
  + apply IHl; auto. intros n b Hn. apply (H (S n) b). assumption.
Qed.

Lemma atom_equiv_Lequiv :
  forall a1 a2,
    atom_equiv a1 a2 ->
    atom_Lequiv auth lab a1 a2.
Proof.
pose proof equiv_Lequiv_strong. tauto.
Qed.

Lemma value_equiv_Lequiv :
  forall v1 v2,
    value_equiv v1 v2 ->
    value_Lequiv auth lab v1 v2.
Proof.
pose proof equiv_Lequiv_strong. tauto.
Qed.

Lemma env_equiv_Lequiv :
  forall e1 e2,
    env_equiv e1 e2 ->
    env_Lequiv auth lab e1 e2.
Proof.
pose proof equiv_Lequiv_strong. tauto.
Qed.

Lemma Lequiv_auth_lab_equiv_strong :
  forall auth' lab',
    auth =A auth' ->
    lab =L lab' ->
    (forall a1 a2,
       atom_Lequiv auth  lab  a1 a2 ->
       atom_Lequiv auth' lab' a1 a2)
    /\ (forall v1 v2,
          value_Lequiv auth  lab  v1 v2 ->
          value_Lequiv auth' lab' v1 v2)
    /\ (forall e1 e2,
          env_Lequiv auth  lab  e1 e2 ->
          env_Lequiv auth' lab' e1 e2).
Proof.
intros auth' lab' HA HL.
apply atom_value_env_mutind; intros; auto.
* destruct a2 as [v2 l2]. intro Hlab'.
  fold (value_Lequiv auth' lab').
  assert (l ⊑[auth]lab \/ l2 ⊑[auth]lab) as Hlab.
  { destruct Hlab'; [left|right]; transitivity lab'; eauto. }
  specialize (H0 Hlab).
  fold (value_Lequiv auth lab) in H0.
  destruct H0. auto.
* destruct v2; try tauto.
  destruct H0 as [Henv Ht].
  fold (atom_Lequiv auth lab) in Henv. fold (env_Lequiv auth lab) in Henv.
  split; auto.
  fold (atom_Lequiv auth' lab'). fold (env_Lequiv auth' lab'). auto.
* generalize dependent e2. induction l; intros l' Henv; destruct l'; auto.
  destruct Henv. split.
  + apply (H 0 a); auto.
  + apply IHl; auto. intros n b Hn. apply (H (S n) b). assumption.
Qed.

Lemma atom_Lequiv_auth_lab_equiv :
  forall auth' lab' a1 a2,
    auth =A auth' ->
    lab =L lab' ->
    atom_Lequiv auth  lab  a1 a2 ->
    atom_Lequiv auth' lab' a1 a2.
Proof.
intros auth' lab' ? ? HA HL.
destruct (Lequiv_auth_lab_equiv_strong auth' lab' HA HL) as [? _].
auto.
Qed.

Lemma value_Lequiv_auth_lab_equiv :
  forall auth' lab' v1 v2,
    auth =A auth' ->
    lab =L lab' ->
    value_Lequiv auth  lab  v1 v2 ->
    value_Lequiv auth' lab' v1 v2.
Proof.
intros auth' lab' ? ? HA HL.
destruct (Lequiv_auth_lab_equiv_strong auth' lab' HA HL) as [_ [? _]].
auto.
Qed.

Lemma env_Lequiv_auth_lab_equiv :
  forall auth' lab' e1 e2,
    auth =A auth' ->
    lab =L lab' ->
    env_Lequiv auth  lab  e1 e2 ->
    env_Lequiv auth' lab' e1 e2.
Proof.
intros auth' lab' ? ? HA HL.
destruct (Lequiv_auth_lab_equiv_strong auth' lab' HA HL) as [_ [_ ?]].
auto.
Qed.

End Compatibility.

Hint Resolve
     atom_equiv_Lequiv
     value_equiv_Lequiv
     env_equiv_Lequiv
     atom_Lequiv_auth_lab_equiv
     value_Lequiv_auth_lab_equiv
     env_Lequiv_auth_lab_equiv.

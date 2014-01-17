Require Import MyTactics.
Require Import Relations.
Require Export PreLattice.

Set Implicit Arguments.

(** * Label algebras *)
Class LabelAlgebra (A: Type) (L: Type)
  :=
{
(** A lower-bounded join-pre-lattice of authorities. *)
  authLeq : relation A
; authLeqPreOrder :> PreOrder authLeq
; authJoinPreLattice :> @JoinPreLattice A authLeq authLeqPreOrder
; authHasBottom :> HasBottom A authLeq

(** A pre-lattice of labels, with a distinguished point [Ldef]. *)
; labLeq : relation L
; labLeqPreOrder :> PreOrder labLeq
; labJoinPreLattice :> @JoinPreLattice L labLeq labLeqPreOrder
; labMeetPreLattice :> @MeetPreLattice L labLeq labLeqPreOrder
; Ldef : L

(** A family of pre-lattices, indexed by authorities. *)
; flowsTo : A -> L -> L -> Prop
; flowsToPreOrder :> forall a, PreOrder (flowsTo a)
; flowsToJoinPreLattice :>
    forall a, @JoinPreLattice L (flowsTo a) (flowsToPreOrder a)
; flowsToMeetPreLattice :>
    forall a, @MeetPreLattice L (flowsTo a) (flowsToPreOrder a)

(** The bottom of the family is the original pre-lattice of labels. *)
; flowsToBottom :
    same_relation L (flowsTo bottom) labLeq
(** All the lattices share the same join and meet as the original lattice. *)
; joinBottom :
    forall (a: A) (l1 l2 : L),
      @join _ (flowsTo a) _ _ l1 l2
      = @join _ labLeq _ _ l1 l2
; meetBottom :
    forall (a: A) (l1 l2 : L),
      @meet _ (flowsTo a) _ _ l1 l2
      = @meet _ labLeq _ _ l1 l2

(** The family is monotone with respect to authorities. *)
; flowsToIncluded :
    forall a1 a2, authLeq a1 a2 -> inclusion _ (flowsTo a1) (flowsTo a2)
}.

(** ** Some notations. *)
Notation "l1 ⊑ l2" := (labLeq l1 l2) (at level 70).
Notation "l1 =L l2" :=
  (@equiv _ (@PreOrder_setoid _ labLeq _) l1 l2) (at level 70).
Notation "l1 ⊔ l2" := (@join _ labLeq _ _ l1 l2) (at level 65).
Notation "l1 ⊓ l2" := (@meet _ labLeq _ _ l1 l2) (at level 65).

Notation "l1 ⊑[ a ] l2" := (flowsTo a l1 l2) (at level 70).
Notation "l1 =L [ a ] l2" :=
  (@equiv _ (@PreOrder_setoid _ (flowsTo a) _) l1 l2) (at level 70).
Notation "l1 ⊔[ a ] l2" := (@join _ (flowsTo a) _ _ l1 l2) (at level 65).
Notation "l1 ⊓[ a ] l2" := (@meet _ (flowsTo a) _ _ l1 l2) (at level 65).

Notation "a1 ≤ a2" := (authLeq a1 a2) (at level 70).
Notation "a1 =A a2" :=
  (@equiv _ (@PreOrder_setoid _ authLeq _) a1 a2) (at level 70).
Notation "a1 ∨ a2" := (@join _ authLeq _ _ a1 a2) (at level 65).

(** ** Some automations hints and facts about label algebras. *)

Hint Extern 1 =>
match goal with
| _ : @Reflexive _ ?R |- ?R _ _ => reflexivity
| _ : @Equivalence _ ?R |- ?R _ _ => reflexivity
| H : Setoid _ |- @equiv _ ?H _ _ => reflexivity
| |- @equiv _ (@PreOrder_setoid _ _ _) _ _ => reflexivity
| H : LabelAlgebra ?L ?A |- @labLeq ?L ?A _ _ _ => reflexivity
| H : LabelAlgebra ?L ?A |- @authLeq ?L ?A _ _ _ => reflexivity
| H : LabelAlgebra ?L ?A |- @flowsTo ?L ?A _ _ _ _ => reflexivity
| H : LabelAlgebra ?L ?A |- authLeq bottom _ => apply bottom_minimum
end.

Section Facts.

Lemma authLeq_join_UBL {A L} {LA: LabelAlgebra A L} :
  forall a1 a2, a1 ≤ a2 ∨ a1.
Proof.
intros a1 a2. apply join_ub2.
Qed.

Lemma authLeq_join_UBR {A L} {LA: LabelAlgebra A L} :
  forall a1 a2, a1 ≤ a1 ∨ a2.
Proof.
intros a1 a2. apply join_ub1.
Qed.

Lemma authLeq_UB_join_L {A L} {LA: LabelAlgebra A L} :
  forall a a1 a2, a2 ∨ a1 ≤ a -> a1 ≤ a.
Proof.
intros a a1 a2 H.
transitivity (a2 ∨ a1); auto using authLeq_join_UBL.
Qed.

Lemma authLeq_UB_join_R {A L} {LA: LabelAlgebra A L} :
  forall a a1 a2, a1 ∨ a2 ≤ a -> a1 ≤ a.
Proof.
intros a a1 a2 H.
transitivity (a1 ∨ a2); auto using authLeq_join_UBR.
Qed.

Lemma authLeq_LUB {A L} {LA: LabelAlgebra A L} :
  forall a a1 a2, a1 ≤ a -> a2 ≤ a -> a1 ∨ a2 ≤ a.
Proof.
intros a a1 a2 H1 H2.
apply join_lub; assumption.
Qed.

Lemma authLeq_flowsTo_flowsTo {A L} {LA: LabelAlgebra A L} :
  forall l1 l2 a a',
    a ≤ a' ->
    l1 ⊑[a] l2 ->
    l1 ⊑[a'] l2.
Proof.
intros l1 l2 a a' Ha Hl.
apply (flowsToIncluded a); assumption.
Qed.

Lemma authEquiv_flowsTo_flowsTo {A L} {LA: LabelAlgebra A L} :
  forall l1 l2 a a',
    a =A a' ->
    l1 ⊑[a] l2 ->
    l1 ⊑[a'] l2.
Proof.
intros l1 l2 a a' [Ha _] Hl.
eapply authLeq_flowsTo_flowsTo; eassumption.
Qed.

Lemma authEquiv_flowsTo_flowsTo' {A L} {LA: LabelAlgebra A L} :
  forall l1 l2 a a',
    a' =A a ->
    l1 ⊑[a] l2 ->
    l1 ⊑[a'] l2.
Proof.
intros l1 l2 a a' [_ Ha] Hl.
eapply authLeq_flowsTo_flowsTo; eassumption.
Qed.

Lemma labLeq_flowsTo {A L} {LA: LabelAlgebra A L} :
  forall l1 l2 a,
    l1 ⊑ l2 ->
    l1 ⊑[a] l2.
Proof.
intros l1 l2 a H.
apply (flowsToIncluded bottom). apply bottom_minimum.
destruct flowsToBottom as [_ Hincl]. apply Hincl. assumption.
Qed.

Lemma labEquiv_flowsTo {A L} {LA: LabelAlgebra A L} :
  forall l1 l2 a,
    l1 =L l2 ->
    l1 ⊑[a] l2.
Proof.
intros l1 l2 a [H _]. apply labLeq_flowsTo. assumption.
Qed.

Lemma labEquiv_flowsTo' {A L} {LA: LabelAlgebra A L} :
  forall l1 l2 a,
    l2 =L l1 ->
    l1 ⊑[a] l2.
Proof.
intros l1 l2 a [_ H]. apply labLeq_flowsTo. assumption.
Qed.

Lemma labEquiv_flowsToEquiv {A L} {LA: LabelAlgebra A L} :
  forall l1 l2 a,
    l2 =L l1 ->
    l1 =L[a] l2.
Proof.
intros l1 l2 a H. split.
apply labEquiv_flowsTo'; assumption.
apply labEquiv_flowsTo; assumption.
Qed.

Lemma flowsToBottom_labLeq {A L} {LA: LabelAlgebra A L} :
  forall l1 l2,
    l1 ⊑[bottom] l2 ->
    l1 ⊑ l2.
Proof.
intros l1 l2 H.
destruct flowsToBottom as [Hincl _]. apply Hincl. assumption.
Qed.

Lemma flowsToEqBottom_labLeq {A L} {LA: LabelAlgebra A L} :
  forall l1 l2,
    l1 =L[bottom] l2 ->
    l1 ⊑ l2.
Proof.
intros l1 l2 [H _]. apply flowsToBottom_labLeq. assumption.
Qed.

Lemma flowsToEqBottom_labLeq' {A L} {LA: LabelAlgebra A L} :
  forall l1 l2,
    l2 =L[bottom] l1 ->
    l1 ⊑ l2.
Proof.
intros l1 l2 [_ H]. apply flowsToBottom_labLeq. assumption.
Qed.

Lemma flowsTo_join_UBL {A L} {LA: LabelAlgebra A L} :
  forall l1 l2 a,
   l1 ⊑[a] l2 ⊔ l1.
Proof.
intros l1 l2 a.
apply (flowsToIncluded bottom). auto.
apply labLeq_flowsTo. apply join_ub2.
Qed.

Lemma flowsTo_join_UBR {A L} {LA: LabelAlgebra A L} :
  forall l1 l2 a,
   l1 ⊑[a] l1 ⊔ l2.
Proof.
intros l1 l2 a.
apply (flowsToIncluded bottom). auto.
apply labLeq_flowsTo. apply join_ub1.
Qed.

Lemma flowsTo_join_LUB {A L} {LA: LabelAlgebra A L} :
  forall l1 l2 l a,
   l1 ⊑[a] l ->
   l2 ⊑[a] l ->
   l1 ⊔ l2 ⊑[a] l.
Proof.
intros l1 l2 l a H1 H2.
rewrite <- (joinBottom a).
apply join_lub; assumption.
Qed.

End Facts.
Hint Resolve
     authLeq_join_UBL
     authLeq_join_UBR
     authLeq_UB_join_L
     authLeq_UB_join_R
     authLeq_LUB
     authLeq_flowsTo_flowsTo
     authEquiv_flowsTo_flowsTo
     authEquiv_flowsTo_flowsTo'
     labLeq_flowsTo
     labEquiv_flowsTo
     labEquiv_flowsTo'
     labEquiv_flowsToEquiv
     flowsToBottom_labLeq
     flowsToEqBottom_labLeq
     flowsToEqBottom_labLeq'
     flowsTo_join_UBL
     flowsTo_join_UBR
     flowsTo_join_LUB.

Lemma labEquiv_join {A L} {LA: LabelAlgebra A L} :
  forall l1 l2 l,
    l1 =L l2 ->
    l1 ⊔ l =L l2 ⊔ l.
Proof.
intros l1 l2 l H.
inversion H as [H1 H2].
assert (H3: l1 ⊑ l1 ⊔ l) by auto.
assert (H4: l2 ⊑ l2 ⊔ l) by auto.
assert (H5: l ⊑ l1 ⊔ l) by auto.
assert (H6: l ⊑ l2 ⊔ l) by auto.
assert (H7: l1 ⊑ l2 ⊔ l) by (transitivity l2; auto).
assert (H8: l2 ⊑ l1 ⊔ l) by (transitivity l1; auto).
split; auto.
Qed.

(** * Packing label algebras with their authority- and label-types. *)
Definition packedLA : Type := { A :Type & { L : Type & LabelAlgebra A L } }.
Definition packLA {A L: Type} (LA: LabelAlgebra A L) : packedLA :=
  existT _ A (existT _ L LA).

(** * Label algebra maps, and applicative structure. *)
Record LAMap
       {A1 L1: Type} {LA1: LabelAlgebra A1 L1}
       {A2 L2: Type} {LA2: LabelAlgebra A2 L2} :=
{ Amap : A1 -> A2
; Lmap : L1 -> L2
}.

Notation "LA1 ==> LA2" := (@LAMap _ _ LA1 _ _ LA2).

Definition LAidentity {A L} (LA: LabelAlgebra A L) : LA ==> LA :=
{| Amap a := a
;  Lmap l := l
|}.

Definition LAcompose
           {A1 L1: Type} {LA1: LabelAlgebra A1 L1}
           {A2 L2: Type} {LA2: LabelAlgebra A2 L2}
           {A3 L3: Type} {LA3: LabelAlgebra A3 L3}
           (m23: LA2 ==> LA3) (m12: LA1 ==> LA2) : LA1 ==> LA3
  :=
{| Amap a := Amap m23 (Amap m12 a)
;  Lmap l := Lmap m23 (Lmap m12 l)
|}.


Class LAMapApply (F: Type -> Type -> Type) :=
{ apply :
    forall {A1 L1: Type} {LA1: LabelAlgebra A1 L1}
           {A2 L2: Type} {LA2: LabelAlgebra A2 L2},
      LA1 ==> LA2 -> F A1 L1 -> F A2 L2
; apply_refl :
    forall {A L: Type} {LA: LabelAlgebra A L} (x: F A L),
      apply (LAidentity LA) x = x
; apply_compose :
    forall {A1 L1: Type} {LA1: LabelAlgebra A1 L1}
           {A2 L2: Type} {LA2: LabelAlgebra A2 L2}
           {A3 L3: Type} {LA3: LabelAlgebra A3 L3}
           (m12: LA1 ==> LA2) (m23: LA2 ==> LA3)
           (x: F A1 L1),
      apply (LAcompose m23 m12) x = apply m23 (apply m12 x)
}.

Instance LAMapApplyAuth : LAMapApply (fun A _ => A) :=
{ apply := @Amap }.
Proof.
* intros A L LA a. reflexivity.
* intros A1 L1 LA1 A2 L2 LA2 A3 L3 LA3 m12 m23 a. reflexivity.
Qed.

Instance LAMapApplyLab : LAMapApply (fun _ L => L) :=
{ apply := @Lmap }.
Proof.
* intros A L LA l. reflexivity.
* intros A1 L1 LA1 A2 L2 LA2 A3 L3 LA3 m12 m23 l. reflexivity.
Qed.

(** * Injective and surjective maps; label algebra morphisms.  *)
Definition LAsurjective {A1 A2 L1 L2}
           {LA1: LabelAlgebra A1 L1} {LA2: LabelAlgebra A2 L2}
           (m: LA1 ==> LA2) : Prop :=
  surjective (@authLeq _ _ LA1) (@authLeq _ _ LA2) (Amap m)
  /\ surjective (@labLeq _ _ LA1) (@labLeq _ _ LA2) (Lmap m).

Definition LAinjective {A1 A2 L1 L2}
           {LA1: LabelAlgebra A1 L1} {LA2: LabelAlgebra A2 L2}
           (m: LA1 ==> LA2) : Prop :=
  injective (@authLeq _ _ LA1) (@authLeq _ _ LA2) (Amap m)
  /\ injective (@labLeq _ _ LA1) (@labLeq _ _ LA2) (Lmap m).

Lemma LAinjective_identity {A L: Type} {LA: LabelAlgebra A L} :
      LAinjective (LAidentity LA).
Proof.
split; intros x y H; assumption.
Qed.

Lemma LAinjective_trans {A1 L1 A2 L2 A3 L3: Type}
      {LA1 : LabelAlgebra A1 L1}
      {LA2 : LabelAlgebra A2 L2}
      {LA3 : LabelAlgebra A3 L3}
      (m12: LA1 ==> LA2) (m23: LA2 ==> LA3) :
  LAinjective m12 ->
  LAinjective m23 ->
  LAinjective (LAcompose m23 m12).
Proof.
intros [HA12 HL12] [HA23 HL23]; split; intros x y H.
* apply HA12. apply HA23. assumption.
* apply HL12. apply HL23. assumption.
Qed.

Definition LAmorphism {A1 A2 L1 L2}
           {LA1: LabelAlgebra A1 L1} {LA2: LabelAlgebra A2 L2}
           (m: LA1 ==> LA2) : Prop :=
  (forall a1 a2, a1 =A a2 -> Amap m a1 =A Amap m a2)
  /\ Amap m bottom =A bottom
  /\ (forall a1 a2, Amap m a1 ∨ Amap m a2 =A Amap m (a1 ∨ a2))
  /\ (forall l1 l2, l1 =L l2 -> Lmap m l1 =L Lmap m l2)
  /\ Lmap m Ldef =L Ldef
  /\ (forall l1 l2, Lmap m l1 ⊔ Lmap m l2 =L Lmap m (l1 ⊔ l2))
  /\ (forall l1 l2, Lmap m l1 ⊓ Lmap m l2 =L Lmap m (l1 ⊓ l2))
  /\ (forall a l1 l2, l1 ⊑[a] l2 -> Lmap m l1 ⊑[Amap m a] Lmap m l2).

Lemma LAmorphism_identity {A L: Type} {LA: LabelAlgebra A L} :
      LAmorphism (LAidentity LA).
Proof.
unfold LAmorphism. splits; auto.
Qed.

Lemma LAmorphism_trans {A1 L1 A2 L2 A3 L3: Type}
      {LA1 : LabelAlgebra A1 L1}
      {LA2 : LabelAlgebra A2 L2}
      {LA3 : LabelAlgebra A3 L3}
      (m12: LA1 ==> LA2) (m23: LA2 ==> LA3) :
  LAmorphism m12 ->
  LAmorphism m23 ->
  LAmorphism (LAcompose m23 m12).
Proof.
intros
  [HAcompat [HAbottom [HAjoin [HLcompat [HLdef [HLjoin [HLmeet Hmon]]]]]]]
  [HAcompat' [HAbottom' [HAjoin' [HLcompat' [HLdef' [HLjoin' [HLmeet' Hmon']]]]]]].
unfold LAmorphism. splits.
* intros a1 a2 H. apply HAcompat'. apply HAcompat. assumption.
* rewrite <- HAbottom'. apply HAcompat'. assumption.
* intros a1 a2.
  transitivity (Amap m23 (Amap m12 a1) ∨ Amap m23 (Amap m12 a2)); try reflexivity.
  rewrite HAjoin'. apply HAcompat'. apply HAjoin.
* intros l1 l2 H. apply HLcompat'. apply HLcompat. assumption.
* rewrite <- HLdef'. apply HLcompat'. assumption.
* intros l1 l2.
  transitivity (Lmap m23 (Lmap m12 l1) ⊔ Lmap m23 (Lmap m12 l2)); try reflexivity.
  rewrite HLjoin'. apply HLcompat'. apply HLjoin.
* intros l1 l2.
  transitivity (Lmap m23 (Lmap m12 l1) ⊓ Lmap m23 (Lmap m12 l2)); try reflexivity.
  rewrite HLmeet'. apply HLcompat'. apply HLmeet.
* intros a l1 l2 H. apply Hmon'. apply Hmon. assumption.
Qed.

Definition LAinjection {A1 A2 L1 L2}
           {LA1: LabelAlgebra A1 L1} {LA2: LabelAlgebra A2 L2}
           (m: LA1 ==> LA2) : Prop :=
  LAmorphism m
  /\ LAinjective m
  /\ (forall a l1 l2, Lmap m l1 ⊑[Amap m a] Lmap m l2 -> l1 ⊑[a] l2).

Lemma LAinjection_identity {A L: Type} {LA: LabelAlgebra A L} :
      LAinjection (LAidentity LA).
Proof.
unfold LAinjection. splits; auto using LAmorphism_identity, LAinjective_identity.
Qed.

Lemma LAinjection_trans {A1 L1 A2 L2 A3 L3: Type}
      {LA1 : LabelAlgebra A1 L1}
      {LA2 : LabelAlgebra A2 L2}
      {LA3 : LabelAlgebra A3 L3}
      (m12: LA1 ==> LA2) (m23: LA2 ==> LA3) :
  LAinjection m12 ->
  LAinjection m23 ->
  LAinjection (LAcompose m23 m12).
Proof.
intros [Hmorph1 [Hinj1 HflowsTo1]] [Hmorph2 [Hinj2 HflowsTo2]].
unfold LAinjection. splits.
* apply LAmorphism_trans; trivial.
* apply LAinjective_trans; trivial.
* auto.
Qed.

Lemma sufficient_monotone {A1 A2 L1 L2}
      {LA1: LabelAlgebra A1 L1} {LA2: LabelAlgebra A2 L2}
      (m: LA1 ==> LA2) :
  Amap m bottom =A bottom ->
  (forall a l1 l2, l1 ⊑[a] l2 -> Lmap m l1 ⊑[Amap m a] Lmap m l2) ->
  forall l1 l2, l1 ⊑ l2 -> Lmap m l1 ⊑ Lmap m l2.
Proof.
intros HAbottom HflowsTo l1 l2 H.
apply flowsToBottom in H. apply HflowsTo in H. eauto.
Qed.

Lemma sufficient_antitone {A1 A2 L1 L2}
      {LA1: LabelAlgebra A1 L1} {LA2: LabelAlgebra A2 L2}
      (m: LA1 ==> LA2) :
  Amap m bottom =A bottom ->
  (forall a l1 l2, Lmap m l1 ⊑[Amap m a] Lmap m l2 -> l1 ⊑[a] l2) ->
  forall l1 l2, Lmap m l1 ⊑ Lmap m l2 -> l1 ⊑ l2.
Proof.
intros HAbottom HflowsTo l1 l2 H.
apply flowsToBottom. apply HflowsTo. auto.
Qed.

Definition LAinjection_prop {A1 A2 L1 L2}
      {LA1: LabelAlgebra A1 L1} {LA2: LabelAlgebra A2 L2}
      (m: LA1 ==> LA2) : Prop :=
  Amap m bottom =A bottom
  /\ (forall a1 a2, a1 ≤ a2 <-> Amap m a1 ≤ Amap m a2)
  /\ (forall a1 a2, Amap m (a1 ∨ a2) ≤ Amap m a1 ∨ Amap m a2)
  /\ Lmap m Ldef =L Ldef
  /\ (forall l1 l2, Lmap m (l1 ⊔ l2) ⊑ Lmap m l1 ⊔ Lmap m l2)
  /\ (forall l1 l2, Lmap m l1 ⊓ Lmap m l2 ⊑ Lmap m (l1 ⊓ l2))
  /\ (forall a l1 l2, l1 ⊑[a] l2 <-> Lmap m l1 ⊑[Amap m a] Lmap m l2).

Lemma LAinjection_iff {A1 A2 L1 L2}
      {LA1: LabelAlgebra A1 L1} {LA2: LabelAlgebra A2 L2}
      (m: LA1 ==> LA2) :
  LAinjection m <-> LAinjection_prop m.
Proof.
split; intro H.
* destruct H as
      [[HAcompat [HAbottom [HAjoin [HLcompat [HLdef [HLjoin [HLmeet Hmon]]]]]]]
         [[HAinj HLinj] HflowsTo]].
  unfold LAinjection_prop. splits; auto.
  + intros a1 a2. destruct (HAjoin a1 a2) as [H1 H2]. split; intro H.
    - assert (a1 ∨ a2 =A a2) as Ha. { split; auto. }
      apply HAcompat in Ha. rewrite <- HAjoin in Ha.
      apply join_characterization. destruct Ha; assumption.
    - assert (a1 ∨ a2 =A a2) as Ha.
      { apply HAinj. rewrite <- HAjoin. split; auto. }
      destruct Ha as [Ha _]. apply join_characterization in Ha.
      assumption.
  + intros a1 a2. specialize (HAjoin a1 a2). destruct HAjoin; assumption.
  + intros a l1 l2. split; auto.
* destruct H as
      [HAbottom [HAiso [HAjoin [HLdef [HLjoin [HLmeet HflowsTo]]]]]].
  unfold LAinjection, LAmorphism, LAinjective. splits; auto.
  + intros a1 a2 [H1 H2]; split; apply HAiso; assumption.
  + intros a1 a2; split; auto.
    apply join_lub; apply HAiso; [ apply join_ub1 | apply join_ub2 ].
  + intros l1 l2 [H1 H2]; split; apply flowsToBottom.
    - apply flowsToBottom in H1; apply HflowsTo in H1; eauto.
    - apply flowsToBottom in H2; apply HflowsTo in H2; eauto.
  + intros l1 l2. split; auto. apply join_lub.
    - assert (Lmap m l1 ⊑[Amap m bottom] Lmap m (l1 ⊔ l2)).
      { apply HflowsTo. auto. }
      eauto.
    - assert (Lmap m l2 ⊑[Amap m bottom] Lmap m (l1 ⊔ l2)).
      { apply HflowsTo. auto. }
      eauto.
  + intros l1 l2. split; auto. apply meet_glb.
    - assert (Lmap m (l1 ⊓ l2) ⊑[Amap m bottom] Lmap m l1).
      { apply HflowsTo. apply flowsToBottom. apply meet_lb1. }
      eauto.
    - assert (Lmap m (l1 ⊓ l2) ⊑[Amap m bottom] Lmap m l2).
      { apply HflowsTo. apply flowsToBottom. apply meet_lb2. }
      eauto.
  + intros a l1 l2 H. apply HflowsTo. assumption.
  + intros a1 a2 [H1 H2]; split; apply HAiso; assumption.
  + intros l1 l2 [H1 H2]; split; apply flowsToBottom; apply HflowsTo; auto.
  + intros a l1 l2 H. apply HflowsTo. assumption.
Qed.

Definition injects_in (LA1 LA2: packedLA) : Prop :=
  exists m: (projT2 (projT2 LA1)) ==> (projT2 (projT2 LA2)),
    LAinjection m.

Notation "LA1 ↪ LA2" :=
  (injects_in (packLA LA1) (packLA LA2)) (at level 70).

Instance injects_in_PreOrder : PreOrder injects_in.
Proof.
constructor.
* intros [A [L LA]]. exists (LAidentity LA). apply LAinjection_identity.
* intros [A1 [L1 LA1]] [A2 [L2 [LA2]]] [A3 [L3 LA3]] [m12 H12] [m23 H23].
  exists (LAcompose m23 m12).
  apply LAinjection_trans; trivial.
Qed.

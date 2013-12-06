Require Import MyTactics.
Require Export List.
Require Import Relations.

(** * [repeat]: definition and facts. *)
Fixpoint repeat {A} (a: A) (n: nat) : list A :=
match n with
| O => nil
| S n => a :: repeat a n
end.

Lemma map_repeat {A B} (f: A -> B) (a: A) (n: nat) :
  map f (repeat a n) = repeat (f a) n.
Proof.
induction n.
* reflexivity.
* simpl. congruence.
Qed.

Lemma repeat_length {A} :
  forall (a: A) n, length (repeat a n) = n.
Proof.
intros a n. induction n; simpl in *; auto.
Qed.

Lemma repeat_nth {A} :
  forall (a a0 : A) k n,
    k < n ->
    nth k (repeat a n) a0 = a.
Proof.
intros a a0 k n H.
generalize dependent k. revert a. induction n; intros a k H; auto.
simpl. destruct k; auto.
Qed.

(** * Facts about [last]. *)
Lemma last_nth {A} :
  forall (l: list A) (default: A),
    last l default = nth (length l - 1) l default.
Proof.
intros l default. induction l.
* reflexivity.
* destruct l as [|b l].
  + reflexivity.
  + transitivity (last (b :: l) default). reflexivity.
    rewrite IHl. simpl.
    replace (length l - 0) with (length l) by auto with arith.
    reflexivity.
Qed.

Lemma last_In {A} :
  forall (l: list A) (default: A),
    l <> nil -> In (last l default) l.
Proof.
intros l default H. destruct l as [|a l].
* exfalso. congruence.
* rewrite last_nth. apply nth_In. auto with arith.
Qed.

Lemma last_map {A B} (f: A -> B):
  forall (l: list A) (default: A),
    last (map f l) (f default) = f (last l default).
Proof.
intros l default. induction l.
* reflexivity.
* simpl map. destruct l as [|b l].
  + reflexivity.
  + transitivity (last (map f (b :: l)) (f default)). reflexivity.
    rewrite IHl. reflexivity.
Qed.

(** * Facts about [app]. *)
Lemma app_comm_cons_cons {A}:
  forall a1 a2 (l1 l2: list A),
    (l1 ++ a1 :: nil) ++ a2 :: l2 = l1 ++ a1 :: a2 :: l2.
Proof.
intros a1 a2 l1.
generalize dependent a2. generalize dependent a1.
induction l1; intros a1 a2 l2.
* reflexivity.
* simpl. f_equal. auto.
Qed.

(** * [atIndex] *)
Fixpoint atIndex {A} (l: list A) (i: nat) {struct i} : option A :=
  match l with
    | nil => None
    | a :: l => match i with
                  | 0 => Some a
                  | S j => atIndex l j
                end
  end.

Lemma atIndexNil {A} (i: nat) : atIndex (@nil A) i = None.
Proof.
destruct i; trivial.
Qed.

Lemma atIndexNilSome {P A} (i: nat) a : atIndex (@nil A) i = Some a -> P.
Proof.
intro H. rewrite atIndexNil in H. inversion H.
Qed.
Hint Extern 1 =>
match goal with
| H: atIndex (@nil _) _ = Some _ |- _ =>
    apply (atIndexNilSome _ _ H)
end.

Lemma atIndexLengthNone {A} (l: list A) (i: nat) :
  length l <= i ->
  atIndex l i = None.
Proof.
intro H. generalize dependent i.
induction l; intros i H; destruct i; simpl in *; auto.
Qed.

Lemma atIndexNoneLength {A} (l: list A) (i: nat) :
  atIndex l i = None ->
  length l <= i.
Proof.
intro H. generalize dependent i.
induction l; intros i H; destruct i; simpl in *; auto with arith.
congruence.
Qed.
Hint Resolve atIndexNoneLength.

Lemma atIndexLengthSome {A} (l: list A) (i: nat) :
  i < length l ->
  exists a, atIndex l i = Some a.
Proof.
intro H.
generalize dependent i; induction l; intros i H;
simpl in *; auto.
destruct i; simpl in *; eauto.
Qed.
Hint Resolve atIndexLengthSome.

Lemma atIndexSomeLength {A} (l: list A) (a: A) (i: nat) :
  atIndex l i = Some a ->
  i < length l.
Proof.
intro H.
generalize dependent i; generalize dependent a; induction l; intros b i H;
simpl in *; auto.
destruct i; simpl in *; auto.
specialize (IHl _ _ H). auto with arith.
Qed.
Hint Resolve atIndexSomeLength.

Lemma atIndexAppL {A} (l1 l2: list A) (i: nat) :
  atIndex (l1 ++ l2) (length l1 + i) = atIndex l2 i.
Proof.
generalize dependent l2. revert i.
induction l1; intros i l2; simpl in *; auto.
Qed.

Lemma atIndexAppLSome {A} (l1 l2: list A) (a: A) (i: nat) :
  atIndex l2 i = Some a ->
  atIndex (l1 ++ l2) (length l1+i) = Some a.
Proof.
intro H. rewrite atIndexAppL. assumption.
Qed.

Lemma atIndexAppR {A} (l1 l2: list A) (i: nat) :
  i < length l1 ->
  atIndex (l1 ++ l2) i = atIndex l1 i.
Proof.
intro H. generalize dependent l2.
generalize dependent i.
induction l1; intros i H l2; simpl in *; auto.
destruct i; simpl in *; auto.
Qed.

Lemma atIndexAppRSome {A} (l1 l2: list A) (a: A) (i: nat) :
  atIndex l1 i = Some a ->
  atIndex (l1 ++ l2) i = Some a.
Proof.
intro H. rewrite atIndexAppR. assumption.
eapply atIndexSomeLength. eassumption.
Qed.

Lemma atIndexAppSome {A} (l1 l2: list A) (a: A) (i: nat) :
  atIndex (l1 ++ l2) i = Some a ->
  atIndex l1 i = Some a \/ atIndex l2 (i - length l1) = Some a.
Proof.
generalize dependent l2. revert i a.
induction l1; intros i b l2 H; simpl in *; auto.
* right. replace (i - 0) with i by auto with arith. assumption.
* destruct i; simpl in *; auto.
Qed.

Lemma atIndexMapNone {A B} (f: A -> B) (l: list A) i :
  atIndex l i = None ->
  atIndex (map f l) i = None.
Proof.
revert i. induction l; intros i H; destruct i; simpl in *; auto; try congruence.
Qed.

Lemma atIndexMapSome {A B} (f: A -> B) (l: list A) a i :
  atIndex l i = Some a ->
  atIndex (map f l) i = Some (f a).
Proof.
revert i a.
induction l; intros i b H; destruct i; simpl in *; eauto; try congruence.
Qed.

Lemma atIndexMapNone_inv {A B} (f: A -> B) (l: list A) i :
  atIndex (map f l) i = None ->
  atIndex l i = None.
Proof.
revert i. induction l; intros i H; destruct i; simpl in *; auto; try congruence.
Qed.

Lemma atIndexMapSome_inv {A B} (f: A -> B) (l: list A) b i :
  atIndex (map f l) i = Some b ->
  exists a, atIndex l i = Some a /\ b = f a.
Proof.
revert i b.
induction l; intros i b H; destruct i; simpl in *; eauto; try congruence.
exists a. split; congruence.
Qed.

(** * [list_forall] *)
Definition list_forall {A} (P: A -> Prop) : list A -> Prop :=
fix list_forall (l: list A) : Prop :=
match l with
| nil => True
| a :: l => P a /\ list_forall l
end.

Lemma list_forall_inclusion {A} (P1 P2: A -> Prop) :
  (forall a, P1 a -> P2 a) ->
  forall l, list_forall P1 l -> list_forall P2 l.
Proof.
intros HP l1 H. induction l1; simpl in *; destruct H; auto.
Qed.

Lemma list_forall_ext {A} (P1 P2: A -> Prop) :
  (forall a, P1 a <-> P2 a) ->
  forall l, list_forall P1 l <-> list_forall P2 l.
Proof.
intros H l. split; apply list_forall_inclusion; firstorder.
Qed.

Lemma list_forall_refl {A} (P: A -> Prop) :
  (forall a, P a) -> forall l, list_forall P l.
Proof.
intros HP l. induction l; simpl; auto.
Qed.

Lemma list_forall_atIndex {A} (P: A -> Prop) :
  forall l n a,
    list_forall P l ->
    atIndex l n = Some a ->
    P a.
Proof.
intro l; induction l; intros n b Hl Ha;
simpl in *; simpl in *; auto.
destruct Hl. destruct n; simpl in *; eauto. congruence.
Qed.

Lemma list_forall_dec {A} (P: A -> Prop) :
  (forall a, { P a } + { ~P a }) ->
  forall (l: list A),
    { list_forall P l } + { exists a, In a l /\ ~ P a }.
Proof.
intros Pdec l. induction l.
* left. exact I.
* simpl. destruct (Pdec a) as [Pa | nPa].
  + destruct IHl as [IHl | IHl].
    - left. apply conj; assumption.
    - right. destruct IHl as [a0 [Hal HnPa]].
      exists a0. split. right. assumption. assumption.
  + right. exists a. split. left. reflexivity. assumption.
Defined.

(** * [list_forall2] *)
Definition list_forall2 {A B} (P: A -> B -> Prop) : list A -> list B -> Prop :=
fix list_forall2 (l1: list A) (l2: list B) {struct l1} : Prop :=
match l1, l2 with
| nil, nil => True
| nil, _ :: _ | _ :: _, nil => False
| a1 :: l1, a2 :: l2 => P a1 a2 /\ list_forall2 l1 l2
end.

Lemma list_forall2_inclusion {A B} (P1 P2: A -> B -> Prop) :
  (forall a b, P1 a b -> P2 a b) ->
  forall la lb, list_forall2 P1 la lb -> list_forall2 P2 la lb.
Proof.
intros HP l1.
induction l1; intros l2 H; destruct l2; simpl in *; destruct H; auto.
Qed.

Lemma list_forall2_ext {A B} (P1 P2: A -> B -> Prop) :
  (forall a b, P1 a b <-> P2 a b) ->
  forall la lb, list_forall2 P1 la lb <-> list_forall2 P2 la lb.
Proof.
intros H la lb. split; apply list_forall2_inclusion; firstorder.
Qed.

Lemma list_forall2_refl {A} (P: A -> A -> Prop) :
  reflexive _ P -> reflexive _ (list_forall2 P).
Proof.
intros HP l. induction l; simpl; auto.
Qed.

Lemma list_forall2_sym {A} (P: A -> A -> Prop) :
  symmetric _ P -> symmetric _ (list_forall2 P).
Proof.
intros HP l1. induction l1; intros l2 H12; destruct l2; simpl in *; intuition.
Qed.

Lemma list_forall2_trans {A} (P: A -> A -> Prop) :
  transitive _ P -> transitive _ (list_forall2 P).
Proof.
intros HP l1.
induction l1; intros l2 l3 H12 H23;
destruct l2; simpl in *; destruct l3; intuition eauto.
Qed.

Lemma list_forall2_atIndex {A B} (P: A -> B -> Prop) :
  forall l1 l2 n a1 a2,
    list_forall2 P l1 l2 ->
    atIndex l1 n = Some a1 ->
    atIndex l2 n = Some a2 ->
    P a1 a2.
Proof.
intro l1; induction l1; intros l2 n a1 a2 Hl Ha1 Ha2;
simpl in *; destruct l2; simpl in *; auto.
destruct Hl. destruct n; simpl in *; eauto. congruence.
Qed.

Lemma list_forall2_atIndex_fun {A B} (P: A -> B -> Prop) :
  forall l1 l2 n a1,
    list_forall2 P l1 l2 ->
    atIndex l1 n = Some a1 ->
    exists a2,
      atIndex l2 n = Some a2 /\ P a1 a2.
Proof.
intro l1; induction l1; intros l2 n a1 Hl Ha1;
simpl in *; destruct l2; simpl in *; auto.
destruct Hl. destruct n; simpl in *; eauto.
inversion Ha1; subst. eauto.
Qed.

Lemma list_forall2_length {A B} (P: A -> B -> Prop) :
  forall l1 l2,
    list_forall2 P l1 l2 ->
    length l1 = length l2.
Proof.
intro l1; induction l1; intros l2 H; destruct l2; simpl in *; auto.
rewrite (IHl1 l2); tauto.
Qed.

(** [combine] *)
Definition combine {A B C} (f: A -> B -> C) : list A -> list B -> list C :=
  fix combine (la: list A) (lb: list B) : list C :=
  match la, lb with
    | nil, _ => nil
    | _, nil => nil
    | a :: la, b :: lb => f a b :: combine la lb
  end.

(** * Missing property about [fold_right] *)
Lemma fold_right_prop_ext (A: Type) (f1 f2: A -> Prop -> Prop)
      (P1 P2: Prop) (l: list A) :
  (forall a P1 P2, (P1 <-> P2) -> (f1 a P1 <-> f2 a P2)) ->
  (P1 <-> P2) ->
  (fold_right f1 P1 l <-> fold_right f2 P2 l).
Proof.
intros Hf HP. induction l.
* assumption.
* simpl. apply Hf. assumption.
Qed.

(** About [conjs] *)
Definition conjs : list Prop -> Prop := fold_right and True.

Lemma conjs_app (l1 l2: list Prop) :
  conjs (l1 ++ l2) <-> conjs l1 /\ conjs l2.
Proof.
revert l2. induction l1; intro l2.
* simpl. tauto.
* simpl. rewrite IHl1. tauto.
Qed.

Lemma conjs_flatten (ps: list (list Prop)) :
  conjs (map conjs ps) <-> conjs (flat_map id ps).
Proof.
unfold conjs. unfold id.
induction ps.
* reflexivity.
* simpl. rewrite IHps. rewrite conjs_app. reflexivity.
Qed.

Lemma conjs_map_forall {A: Type} (P: A -> Prop) (l: list A) :
  list_forall P l = conjs (map P l).
Proof.
unfold conjs. induction l.
* reflexivity.
* simpl. congruence.
Qed.

Fixpoint map2 {A B C: Type} (f: A -> B -> C) (c: C)
           (lA: list A) (lB: list B) : list C :=
  match lA, lB with
    | nil, nil => nil
    | nil, _ | _, nil => c :: nil
    | a :: lA, b :: lB => f a b :: map2 f c lA lB
  end.

Lemma conjs_map2_forall2 {A B: Type} (P: A -> B -> Prop)
      (lA : list A) (lB : list B) :
  list_forall2 P lA lB <-> conjs (map2 P False lA lB).
Proof.
unfold conjs. revert lB. induction lA; intro lB.
* simpl. destruct lB; simpl; tauto.
* simpl. destruct lB; simpl.
  + tauto.
  + rewrite IHlA. tauto.
Qed.

Fixpoint flat_map2 {A B C: Type} (f: A -> B -> list C) (c: C)
         (lA: list A) (lB: list B) : list C :=
  match lA, lB with
    | nil, nil => nil
    | nil, _ | _, nil => c :: nil
    | a :: lA, b :: lB => f a b ++ flat_map2 f c lA lB
  end.

Lemma conjs_flatten2 {A B: Type} (f: A -> B -> list Prop)
      (lA: list A) (lB: list B) :
  conjs (map2 (fun a b => conjs (f a b)) False lA lB)
  <-> conjs (flat_map2 f False lA lB).
Proof.
revert lB. induction lA; intros lB.
* simpl. reflexivity.
* simpl. destruct lB.
  + reflexivity.
  + unfold conjs at 4. rewrite fold_right_app. fold conjs.
    transitivity
      (fold_right and (conjs (map2 (fun a b => conjs (f a b)) False lA lB)) (f a b)).
    - unfold conjs at 4. rewrite <- fold_right_app. fold conjs.
      rewrite conjs_app. reflexivity.
    - apply fold_right_prop_ext; [ tauto | auto ].
Qed.

Lemma conjs_flatmap2_forall2 {A B: Type} (f: A -> B -> list Prop)
      (lA: list A) (lB: list B) :
  list_forall2 (fun a b => conjs (f a b)) lA lB
  <-> conjs (flat_map2 f False lA lB).
Proof.
rewrite conjs_map2_forall2. apply conjs_flatten2.
Qed.

Lemma conjs_list_forall2_bis {A: Type} (f: (A -> Prop) -> A -> Prop)
      (Pt: list (list (A -> Prop))) (t: list (list A)) :
    list_forall2 (list_forall2 f) Pt t
    <->
    conjs (flat_map2 (map2 f False) False Pt t).
Proof.
rewrite <- conjs_flatmap2_forall2.
apply list_forall2_ext.
apply conjs_map2_forall2.
Qed.

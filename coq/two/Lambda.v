Require Import Arith List Omega.

Require Import FunctionalExtensionality.

Lemma functional_extensionality_ex :
  forall {A : Type} (f g : A -> Prop),
    (forall x, f x = g x) ->
    (exists x, f x) = (exists x, g x).
Proof.
  intros. apply functional_extensionality in H. subst. reflexivity.
Qed.

Definition pair_lt (a b : nat * nat) : Prop :=
  fst a + snd a < fst b + snd b.

Lemma pair_lt_wf' :
  forall s a, fst a + snd a <= s -> Acc pair_lt a.
Proof.
  induction s; intros a H1.
  - destruct a as [a1 a2]; destruct a1; destruct a2;
    apply Acc_intro; intros y H2; inversion H1; inversion H2.
  - inversion H1 as [H2 | n H2 Heq]; auto.
    apply Acc_intro. intros y H3. apply IHs. inversion H3; omega.
Defined.

Theorem pair_lt_wf : well_founded pair_lt.
Proof.
  unfold well_founded; intro; eapply pair_lt_wf'; eauto.
Defined.

Inductive term : Type :=
  | TBool : bool -> term
  | TNat : nat -> term
  | TVar : nat -> term
  | TAbs : term -> term
  | TApp : term -> term -> term.

Inductive value : Type :=
  | VBool : bool -> value
  | VNat : nat -> value
  | VClos : list value -> term -> value.

Definition env : Type := list value.

Fixpoint lookup (e : env) (n : nat) : option value :=
  match e with
    | nil => None
    | v :: e' =>
      match n with
        | 0 => Some v
        | S n' => lookup e' n'
      end
  end.

Definition eval_kl : nat * nat -> env -> term -> value -> Prop.
  refine
    (Fix pair_lt_wf (fun _ => env -> term -> value -> Prop)
         (fun kl eval_kl =>
            fun e t v =>
              match t with
                | TBool b =>
                  v = VBool b
                | TNat n =>
                  v = VNat n
                | TVar n =>
                  lookup e n = Some v
                | TAbs t' =>
                  v = VClos e t'
                | TApp t1 t2 =>
                  if Compare_dec.zerop (fst kl) then False
                  else let eval := eval_kl (fst kl - 1, snd kl) _ in
                       exists e1' t1' v2,
                         eval e t1 (VClos e1' t1') /\
                         eval e t2 v2 /\
                         eval (v2 :: e1') t1' v
              end)).
  unfold pair_lt. simpl. omega.
Defined.

Lemma eval_kl_eq :
  forall kl,
    eval_kl kl =
    fun e t v =>
      match t with
        | TBool b => v = VBool b
        | TNat n => v = VNat n
        | TVar n => lookup e n = Some v
        | TAbs t' => v = VClos e t'
        | TApp t1 t2 => (if Compare_dec.zerop (fst kl) then False
                         else let eval := eval_kl (fst kl - 1, snd kl) in
                              exists e1' t1' v2,
                                eval e t1 (VClos e1' t1') /\
                                eval e t2 v2 /\
                                eval (v2 :: e1') t1' v)
      end.
Proof.
  intro kl.
  apply (Fix_eq pair_lt_wf (fun _ => env -> term -> value -> Prop)); intros;
  destruct x as [x1 x2].
  apply functional_extensionality; intro e.
  apply functional_extensionality; intro t.
  apply functional_extensionality; intro v.
  destruct t; try reflexivity.
  destruct x1; auto; simpl.
  apply functional_extensionality_ex; intro e1'.
  apply functional_extensionality_ex; intro t1'.
  apply functional_extensionality_ex; intro v2.
  assert (H': forall (y : nat * nat), f y = g y) by
      (intro; apply functional_extensionality; apply H);
    rewrite H'.
  reflexivity.
Qed.

Lemma eval_k_bool :
  forall k l e b,
    eval_kl (k, l) e (TBool b) (VBool b).
Proof. intros. rewrite eval_kl_eq. reflexivity. Qed.

Lemma eval_kl_bool_inv :
  forall k l e b v,
    eval_kl (k, l) e (TBool b) v -> v = VBool b.
Proof. intros. destruct v; destruct k; destruct l; inversion H; reflexivity. Qed.

Lemma eval_kl_nat :
  forall k l e n,
    eval_kl (k, l) e (TNat n) (VNat n).
Proof. intros. rewrite eval_kl_eq. reflexivity. Qed.

Lemma eval_kl_nat_inv :
  forall k l e n v,
    eval_kl (k, l) e (TNat n) v -> v = VNat n.
Proof. intros. destruct v; destruct k; destruct l; inversion H; reflexivity. Qed.

Lemma eval_kl_var :
  forall k l e n v,
    eval_kl (k, l) e (TVar n) v -> lookup e n = Some v.
Proof. intros. rewrite eval_kl_eq in H. assumption. Qed.

Lemma eval_kl_var_inv :
  forall k l e n v,
    eval_kl (k, l) e (TVar n) v -> lookup e n = Some v.
Proof. intros. destruct v; destruct k; destruct l; inversion H; reflexivity. Qed.

Lemma eval_kl_abs :
  forall k l e t',
    eval_kl (k, l) e (TAbs t') (VClos e t').
Proof. intros. rewrite eval_kl_eq. reflexivity. Qed.

Lemma eval_kl_abs_inv :
  forall k l e t v,
    eval_kl (k, l) e (TAbs t) v -> v = VClos e t.
Proof. intros. destruct v; destruct k; destruct l; inversion H; reflexivity. Qed.

Lemma eval_kl_app :
  forall k l e t1 t2 e1' t1' v2 v3,
    eval_kl (k, l) e t1 (VClos e1' t1') ->
    eval_kl (k, l) e t2 v2 ->
    eval_kl (k, l) (v2 :: e1') t1' v3 ->
    eval_kl (S k, l) e (TApp t1 t2) v3.
Proof.
  intros. rewrite eval_kl_eq. simpl.
  replace (k - 0) with k by omega.
  exists e1'. exists t1'. exists v2.
  split; try split; assumption.
Qed.

Lemma eval_kl_app_inv :
  forall k l e t1 t2 v,
    eval_kl (k, l) e (TApp t1 t2) v ->
    exists k' e1' t1' v2,
      k = S k' /\
      eval_kl (k', l) e t1 (VClos e1' t1') /\
      eval_kl (k', l) e t2 v2 /\
      eval_kl (k', l) (v2 :: e1') t1' v.
Proof.
  intros.
  rewrite eval_kl_eq in H.
  destruct k; simpl in H.
  - inversion H.
  - destruct H as [e1' [t1' [v2 [H1 [H2 H3]]]]].
    replace (k - 0) with k in * by omega.
    exists k. exists e1'. exists t1'. exists v2.
    split; try split; try split; assumption.
Qed.

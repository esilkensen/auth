Require Import Arith List Omega.

Require Import FunctionalExtensionality.

Lemma functional_extensionality_ex :
  forall {A : Type} (f g : A -> Prop),
    (forall x, f x = g x) ->
    (exists x, f x) = (exists x, g x).
Proof.
  intros. apply functional_extensionality in H. subst. reflexivity.
Qed.

Inductive term : Type :=
  | TBool : bool -> term
  | TVar : nat -> term
  | TAbs : term -> term
  | TApp : term -> term -> term.

Inductive value : Type :=
  | VBool : bool -> value
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

Definition eval_k : nat -> env -> term -> value -> Prop.
  refine
    (Fix lt_wf (fun _ => env -> term -> value -> Prop)
         (fun k eval_k =>
            fun e t v =>
              match t with
                | TBool b =>
                  v = VBool b
                | TVar n =>
                  lookup e n = Some v
                | TAbs t' =>
                  v = VClos e t'
                | TApp t1 t2 =>
                  if Compare_dec.zerop k then False
                  else let eval := eval_k (k - 1) _ in
                       exists e1' t1' v2,
                         eval e t1 (VClos e1' t1') /\
                         eval e t2 v2 /\
                         eval (v2 :: e1') t1' v
              end)).
  omega.
Defined.

Lemma eval_k_eq :
  forall k,
    eval_k k =
    fun e t v =>
      match t with
        | TBool b => v = VBool b
        | TVar n => lookup e n = Some v
        | TAbs t' => v = VClos e t'
        | TApp t1 t2 => (if Compare_dec.zerop k then False
                         else let eval := eval_k (k - 1) in
                              exists e1' t1' v2,
                                eval e t1 (VClos e1' t1') /\
                                eval e t2 v2 /\
                                eval (v2 :: e1') t1' v)
      end.
Proof.
  intro k.
  apply (Fix_eq lt_wf (fun _ => env -> term -> value -> Prop)); intros.
  apply functional_extensionality; intro e.
  apply functional_extensionality; intro t.
  apply functional_extensionality; intro v.
  destruct t; try reflexivity.
  destruct x; auto; simpl.
  apply functional_extensionality_ex; intro e1'.
  apply functional_extensionality_ex; intro t1'.
  apply functional_extensionality_ex; intro v2.
  assert (H': forall (y : nat), f y = g y) by
      (intro; apply functional_extensionality; apply H);
    rewrite H'.
  reflexivity.
Qed.

Lemma eval_k_bool :
  forall k e b,
    eval_k k e (TBool b) (VBool b).
Proof. intros. rewrite eval_k_eq. reflexivity. Qed.

Lemma eval_k_bool_inv :
  forall k e b v,
    eval_k k e (TBool b) v -> v = VBool b.
Proof. intros. destruct v; destruct k; inversion H; reflexivity. Qed.

Lemma eval_k_var :
  forall k e n v,
    eval_k k e (TVar n) v -> lookup e n = Some v.
Proof. intros. rewrite eval_k_eq in H. assumption. Qed.

Lemma eval_k_var_inv :
  forall k e n v,
    eval_k k e (TVar n) v -> lookup e n = Some v.
Proof. intros. destruct v; destruct k; inversion H; reflexivity. Qed.

Lemma eval_k_abs :
  forall k e t',
    eval_k k e (TAbs t') (VClos e t').
Proof. intros. rewrite eval_k_eq. reflexivity. Qed.

Lemma eval_k_abs_inv :
  forall k e t v,
    eval_k k e (TAbs t) v -> v = VClos e t.
Proof. intros. destruct v; destruct k; inversion H; reflexivity. Qed.

Lemma eval_k_app :
  forall k e t1 t2 e1' t1' v2 v3,
    eval_k k e t1 (VClos e1' t1') ->
    eval_k k e t2 v2 ->
    eval_k k (v2 :: e1') t1' v3 ->
    eval_k (S k) e (TApp t1 t2) v3.
Proof.
  intros. rewrite eval_k_eq. simpl.
  replace (k - 0) with k by omega.
  exists e1'. exists t1'. exists v2.
  split; try split; assumption.
Qed.

Lemma eval_k_app_inv :
  forall k e t1 t2 v,
    eval_k k e (TApp t1 t2) v ->
    exists k' e1' t1' v2,
      k = S k' /\
      eval_k k' e t1 (VClos e1' t1') /\
      eval_k k' e t2 v2 /\
      eval_k k' (v2 :: e1') t1' v.
Proof.
  intros.
  rewrite eval_k_eq in H.
  destruct k; simpl in H.
  - inversion H.
  - destruct H as [e1' [t1' [v2 [H1 [H2 H3]]]]].
    replace (k - 0) with k in * by omega.
    exists k. exists e1'. exists t1'. exists v2.
    split; try split; try split; assumption.
Qed.

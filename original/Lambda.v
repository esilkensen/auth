Require Export MyList.
Require Import LabelAlgebra.

Set Implicit Arguments.

(** * A small lambda calculus, in de Bruijn notation. *)
Inductive term (A L: Type) : Type :=
| TBool: bool -> term A L
| TNat: nat -> term A L
| TVar: nat -> term A L
| TLam: term A L -> term A L
| TApp: term A L -> term A L -> term A L
| TRelabel: term A L -> A -> L -> term A L
.

Arguments TBool [A L] _.
Arguments TNat  [A L] _.
Arguments TVar  [A L] _.

(** * Application of LA-maps on it. *)
Fixpoint LA_apply_term
         {A1 L1} {LA1: LabelAlgebra A1 L1}
         {A2 L2} {LA2: LabelAlgebra A2 L2}
         (m: LA1 ==> LA2) (t: term A1 L1) : term A2 L2 :=
match t with
| TBool b        => TBool b
| TNat n         => TNat n
| TVar n         => TVar n
| TLam t         => TLam (LA_apply_term m t)
| TApp t1 t2     => TApp (LA_apply_term m t1) (LA_apply_term m t2)
| TRelabel t a l => TRelabel (LA_apply_term m t) (Amap m a) (Lmap m l)
end.

Instance LAMapApplyTerm : LAMapApply term :=
{| apply := @LA_apply_term |}.
Proof.
* intros A L LA t. induction t; simpl; auto; try congruence.
* intros A1 L1 LA1 A2 L2 LA2 A3 L3 LA3 m12 m23 t.
  induction t; simpl; auto; try congruence.
Defined.

(** ** Simplification lemmas and tactics. *)
Section Simpl_apply_term.

Context {A1 L1} {LA1: LabelAlgebra A1 L1}
        {A2 L2} {LA2: LabelAlgebra A2 L2}
        (m: LA1 ==> LA2).

Lemma simpl_apply_term_bool : forall b, apply m (TBool b) = TBool b.
Proof.
reflexivity.
Qed.

Lemma simpl_apply_term_nat : forall n, apply m (TNat n) = TNat n.
Proof.
reflexivity.
Qed.

Lemma simpl_apply_term_var : forall n, apply m (TVar n) = TVar n.
Proof.
reflexivity.
Qed.

Lemma simpl_apply_term_lam : forall t, apply m (TLam t) = TLam (apply m t).
Proof.
reflexivity.
Qed.

Lemma simpl_apply_term_app :
  forall t1 t2, apply m (TApp t1 t2) = TApp (apply m t1) (apply m t2).
Proof.
reflexivity.
Qed.

Lemma simpl_apply_term_relabel :
  forall t a l, apply m (TRelabel t a l) = TRelabel (apply m t) (Amap m a) (Lmap m l).
Proof.
reflexivity.
Qed.

End Simpl_apply_term.

Hint Rewrite
     @simpl_apply_term_bool
     @simpl_apply_term_nat
     @simpl_apply_term_var
     @simpl_apply_term_lam
     @simpl_apply_term_app
     @simpl_apply_term_relabel.

(** * Atoms, values. *)
Section Atoms.

Variable A L : Type.

Inductive atom : Type :=
| Atom: value -> L -> atom
with value : Type :=
| VBool: bool -> value
| VNat: nat -> value
| VClos: list atom -> term A L -> value.

Definition env := list atom.

(** Mutual folds. *)
Section folds.
Hypothesis (Patom: atom -> Type).
Hypothesis (Pvalue: value -> Type).
Hypothesis (Penv: list atom -> Type).
Hypothesis (Hatom: forall v, Pvalue v -> forall l, Patom (Atom v l)).
Hypothesis (Hbool: forall b, Pvalue (VBool b)).
Hypothesis (Hnat: forall n, Pvalue (VNat n)).
Hypothesis (Hclos: forall l, Penv l -> forall t, Pvalue (VClos l t)).
Hypothesis (Henv:  forall l, (forall n a, atIndex l n = Some a -> Patom a) -> Penv l).

Definition env_fold'
           (atom_fold : forall a, Patom a) (e: env) : Penv e :=
  Henv
    e
    ((fix env_fold (e: env) :
        forall n a, atIndex e n = Some a -> Patom a :=
        match e as e
              return forall n a, atIndex e n = Some a -> Patom a
        with
          | nil =>
            fun n a H => atIndexNilSome n a H
          | a :: e =>
            fun n =>
              match n as n
                    return
                    forall b, atIndex (a :: e) n = Some b -> Patom b
              with
                | O => fun b Heq =>
                         match Heq with
                           | eq_refl => atom_fold a
                         end
                | S n => env_fold e n
              end
        end) e).

Fixpoint atom_fold (a: atom) : Patom a :=
match a with
| Atom v l => Hatom (value_fold v) l
end
with value_fold (v: value) : Pvalue v :=
match v with
| VBool b     => Hbool b
| VNat n      => Hnat n
| VClos e t => Hclos (env_fold' atom_fold e) t
end.

Definition env_fold : forall e, Penv e := env_fold' atom_fold.

Definition atom_value_env_fold :
  (forall a, Patom a)
  * (forall v, Pvalue v)
  * (forall e, Penv e) :=
pair (pair atom_fold value_fold) env_fold.

End folds.

(** Mutual induction. *)
Section mutind.

Hypothesis (Patom: atom -> Prop).
Hypothesis (Pvalue: value -> Prop).
Hypothesis (Penv: env -> Prop).
Hypothesis (Hatom: forall v, Pvalue v -> forall l, Patom (Atom v l)).
Hypothesis (Hbool: forall b, Pvalue (VBool b)).
Hypothesis (Hnat: forall n, Pvalue (VNat n)).
Hypothesis (Hclos: forall l, Penv l -> forall t, Pvalue (VClos l t)).
Hypothesis (Henv:  forall l, (forall n a, atIndex l n = Some a -> Patom a) -> Penv l).

Definition atom_value_env_mutind :
  (forall a, Patom a)
  /\ (forall v, Pvalue v)
  /\ (forall e, Penv e) :=
  conj (atom_fold Patom Pvalue Penv Hatom Hbool Hnat Hclos Henv)
       (conj (value_fold Patom Pvalue Penv Hatom Hbool Hnat Hclos Henv)
             (env_fold Patom Pvalue Penv Hatom Hbool Hnat Hclos Henv)).

End mutind.

End Atoms.

Arguments VBool [A L] _.
Arguments VNat  [A L] _.

Section apply.

Hypotheses A1 L1 : Type.
Hypothesis LA1: LabelAlgebra A1 L1.
Hypotheses A2 L2 : Type.
Hypothesis LA2: LabelAlgebra A2 L2.
Hypothesis m: LA1 ==> LA2.

Fixpoint LA_apply_atom (a: atom A1 L1) : atom A2 L2 :=
match a with
| Atom v l => Atom (LA_apply_value v) (Lmap m l)
end
with LA_apply_value (v: value A1 L1) : value A2 L2 :=
match v with
| VBool b => VBool b
| VNat n => VNat n
| VClos e t =>
  VClos (map LA_apply_atom e) (apply m t)
end.

Definition LA_apply_env : env A1 L1 -> env A2 L2 :=
  map LA_apply_atom.

End apply.

Lemma LA_apply_atom_value_env_identity
      A L (LA: LabelAlgebra A L) :
  (forall a, LA_apply_atom (LAidentity LA) a = a)
  /\ (forall v, LA_apply_value (LAidentity LA) v = v)
  /\ (forall e, LA_apply_env (LAidentity LA) e = e).
Proof.
apply atom_value_env_mutind; intros; simpl.
* transitivity (Atom (LA_apply_value (LAidentity LA) v) l).
  + reflexivity.
  + congruence.
* reflexivity.
* reflexivity.
* transitivity (VClos (LA_apply_env (LAidentity LA) l) t).
  + unfold LA_apply_value. simpl. f_equal.
    apply (@apply_refl term LAMapApplyTerm _ _ LA t).
  + congruence.
* induction l; simpl in *; auto. f_equal.
  - apply (H 0 a). reflexivity.
  - apply IHl. intros n b. apply (H (S n) b).
Qed.

Lemma LA_apply_atom_value_env_compose
      (A1 L1: Type) (LA1: LabelAlgebra A1 L1)
      (A2 L2: Type) (LA2: LabelAlgebra A2 L2)
      (A3 L3: Type) (LA3: LabelAlgebra A3 L3)
      (m12: LA1 ==> LA2) (m23: LA2 ==> LA3):
      (forall a,
         LA_apply_atom (LAcompose m23 m12) a
         = LA_apply_atom m23 (LA_apply_atom m12 a))
      /\ (forall v,
            LA_apply_value (LAcompose m23 m12) v
            = LA_apply_value m23 (LA_apply_value m12 v))
      /\ (forall e,
            LA_apply_env (LAcompose m23 m12) e
            = LA_apply_env m23 (LA_apply_env m12 e)).
Proof.
apply atom_value_env_mutind; intros; simpl.
* unfold LA_apply_atom at 1. fold (LA_apply_value (LAcompose m23 m12) v).
  rewrite H. reflexivity.
* reflexivity.
* reflexivity.
* unfold LA_apply_value at 1.
  fold (LA_apply_atom (LAcompose m23 m12)).
  fold (LA_apply_env (LAcompose m23 m12) l).
  rewrite H.
  rewrite (apply_compose _ _ t).
  reflexivity.
* induction l; simpl in *; auto. f_equal.
  - apply (H 0 a). reflexivity.
  - apply IHl. intros n b. apply (H (S n) b).
Qed.

Instance LAMapApplyAtom : LAMapApply atom :=
{ apply := LA_apply_atom }.
Proof.
* intros A L LA a. destruct (LA_apply_atom_value_env_identity LA) as [? _].
  auto.
* intros A1 L1 LA1 A2 L2 LA2 A3 L3 LA3 m12 m23 a.
  destruct (LA_apply_atom_value_env_compose m12 m23) as [? _].
  auto.
Defined.

Instance LAMapApplyValue : LAMapApply value :=
{ apply := LA_apply_value }.
Proof.
* intros A L LA a. destruct (LA_apply_atom_value_env_identity LA) as [_ [? _]].
  auto.
* intros A1 L1 LA1 A2 L2 LA2 A3 L3 LA3 m12 m23 a.
  destruct (LA_apply_atom_value_env_compose m12 m23) as [_ [? _]].
  auto.
Defined.

Instance LAMapApplyEnv : LAMapApply env :=
{ apply := LA_apply_env }.
Proof.
* intros A L LA a. destruct (LA_apply_atom_value_env_identity LA) as [_ [_ ?]].
  auto.
* intros A1 L1 LA1 A2 L2 LA2 A3 L3 LA3 m12 m23 a.
  destruct (LA_apply_atom_value_env_compose m12 m23) as [_ [_ ?]].
  auto.
Defined.

(** * Its semantics: big step evaluation judgment. *)
Reserved Notation "pc ; e ⊢ t ⇓ a" (at level 70).
Inductive eval {A L} {LA: LabelAlgebra A L} :
  L -> env A L -> term A L -> atom A L -> Prop :=
| Eval_bool : forall pc e b,
(* ------------------------------------- *)
    pc; e ⊢ TBool b ⇓ Atom (VBool b) pc
| Eval_nat : forall pc e n,
(* ------------------------------------- *)
    pc; e ⊢ TNat n ⇓ Atom (VNat n) pc
| Eval_var : forall pc e n v l,
    atIndex e n = Some (Atom v l) ->
(* ---------------------------------- *)
    pc; e ⊢ TVar n ⇓ Atom v (l ⊔ pc)
| Eval_lam : forall pc e t,
(* -------------------------------------- *)
    pc; e ⊢ TLam t ⇓ Atom (VClos e t) pc
| Eval_app : forall pc e t1 t2 e1' t1' l1 a2 a3,
    pc; e ⊢ t1 ⇓ Atom (VClos e1' t1') l1 ->
    pc; e ⊢ t2 ⇓ a2 ->
    l1; a2 :: e1' ⊢ t1' ⇓ a3 ->
(* ----------------------------------------- *)
    pc; e ⊢ TApp t1 t2 ⇓ a3
| Eval_relabel : forall pc e t a l v1 l1,
    pc; e ⊢ t ⇓ Atom v1 l1 ->
    l1 ⊑[a] l ->
(* ------------------------------------ *)
    pc; e ⊢ TRelabel t a l ⇓ Atom v1 l
where "pc ; e ⊢ t ⇓ a" := (@eval _ _ _ pc e t a).

Hint Constructors eval.

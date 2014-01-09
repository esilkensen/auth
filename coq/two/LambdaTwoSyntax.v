Require Export MyList.
Require Export LabelAlgebra.
Require Export Two.

Set Implicit Arguments.

(** * A small lambda calculus, in de Bruijn notation. *)
Inductive term : Type :=
  | TBool : bool -> term
  | TNat : nat -> term
  | TVar : nat -> term
  | TAbs : term -> term
  | TApp : term -> term -> term
  | TDecl : term -> term.

(** * Atoms, values. *)
Section Atoms.

Inductive atom : Type :=
  | Atom : value -> two -> atom
with value : Type :=
     | VBool : bool -> value
     | VNat : nat -> value
     | VClos : list atom -> term -> value.

Definition env := list atom.

(** Mutual folds. *)
Section folds.
Hypothesis
  (Patom : atom -> Type).
Hypothesis
  (Pvalue : value -> Type).
Hypothesis
  (Penv : list atom -> Type).
Hypothesis
  (Hatom : forall v, Pvalue v -> forall l, Patom (Atom v l)).
Hypothesis
  (Hbool : forall b, Pvalue (VBool b)).
Hypothesis
  (Hnat : forall n, Pvalue (VNat n)).
Hypothesis
  (Hclos : forall l, Penv l -> forall t, Pvalue (VClos l t)).
Hypothesis
  (Henv : forall l, (forall n a, atIndex l n = Some a -> Patom a) -> Penv l).

Definition env_fold'
           (atom_fold : forall a, Patom a) (e: env) : Penv e :=
  Henv
    e
    ((fix env_fold (e : env) :
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

Fixpoint atom_fold (a : atom) : Patom a :=
match a with
  | Atom v l => Hatom (value_fold v) l
end
with value_fold (v : value) : Pvalue v :=
       match v with
         | VBool b => Hbool b
         | VNat n => Hnat n
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

Hypothesis
  (Patom : atom -> Prop).
Hypothesis
  (Pvalue : value -> Prop).
Hypothesis
  (Penv : env -> Prop).
Hypothesis
  (Hatom : forall v, Pvalue v -> forall l, Patom (Atom v l)).
Hypothesis
  (Hbool : forall b, Pvalue (VBool b)).
Hypothesis
  (Hnat : forall n, Pvalue (VNat n)).
Hypothesis
  (Hclos : forall l, Penv l -> forall t, Pvalue (VClos l t)).
Hypothesis
  (Henv :  forall l, (forall n a, atIndex l n = Some a -> Patom a) -> Penv l).

Definition atom_value_env_mutind :
  (forall a, Patom a)
  /\ (forall v, Pvalue v)
  /\ (forall e, Penv e) :=
  conj (atom_fold Patom Pvalue Penv Hatom Hbool Hnat Hclos Henv)
       (conj (value_fold Patom Pvalue Penv Hatom Hbool Hnat Hclos Henv)
             (env_fold Patom Pvalue Penv Hatom Hbool Hnat Hclos Henv)).

End mutind.

End Atoms.

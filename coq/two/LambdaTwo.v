Require Export LambdaTwoSyntax.
Require Export IndistinguishabilityTwo.

Reserved Notation "[ L , P , k ] pc ; e ⊢ t ⇓ a" (at level 70).
Inductive eval :
  two -> (value -> value -> Prop) -> nat ->
  two -> env -> term -> atom -> Prop :=

| E_Nat : forall L P k pc e n,
(* ------------------------------------------------------ *)
    [L, P, k] pc; e ⊢ TNat n ⇓ Atom (VNat n) pc

| E_Var : forall L P k pc e n v l,
    atIndex e n = Some (Atom v l) ->
(* ------------------------------------------------------ *)
    [L, P, k] pc; e ⊢ TVar n ⇓ Atom v (l ⊔ pc)

| E_Abs : forall L P k pc e t,
(* ------------------------------------------------------ *)
    [L, P, k] pc; e ⊢ TLam t ⇓ Atom (VClos e t) pc

| E_App : forall L P k pc e t1 t2 e1' t1' l1 a2 a3,
    [L, P, k] pc; e ⊢ t1 ⇓ Atom (VClos e1' t1') l1 ->
    [L, P, k] pc; e ⊢ t2 ⇓ a2 ->
    [L, P, k] l1; a2 :: e1' ⊢ t1' ⇓ a3 ->
(* ------------------------------------------------------ *)
    [L, P, k] pc; e ⊢ TApp t1 t2 ⇓ a3

| E_Decl1 : forall L P k pc e t1 t2 v,
    [L, P, k] pc; e ⊢ TApp t1 t2 ⇓ Atom v Bottom2 ->
(* ------------------------------------------------------ *)
    [L, P, k] pc; e ⊢ TDecl t1 t2 ⇓ Atom v Bottom2

(*| E_Decl2 : forall L P k pc e t1 t2 e1' t1' l1 a2 v3,
    [L, P, k] pc; e ⊢ t1 ⇓ Atom (VClos e1' t1') l1 ->
    [L, P, k] pc; e ⊢ t2 ⇓ a2 ->
    [L, P, k] l1; a2 :: e1' ⊢ t1' ⇓ Atom v3 Top2 ->
    (forall a a' v v',
       atom_LPequiv L P a a' ->
       [L, P, k] l1; a :: e1' ⊢ t1' ⇓ Atom v Top2 ->
       [L, P, k] l1; a' :: e1' ⊢ t1' ⇓ Atom v' Top2 ->
       value_Lequiv L v v') ->
(* ------------------------------------------------------ *)
    [L, P, (S k)] pc; e ⊢ TDecl t1 t2 ⇓ Atom v3 Bottom2*)

where "[ L , P , k ] pc ; e ⊢ t ⇓ a" := (eval L P k pc e t a).

Hint Constructors eval.

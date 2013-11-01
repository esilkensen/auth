Require Export LambdaTwoSyntax.
Require Export IndistinguishabilityTwo.

Reserved Notation "[ L , P ] pc ; e ⊢ t ⇓ a" (at level 70).
Inductive eval :
  two -> (value -> value -> Prop) ->
  two -> env -> term -> option atom -> Prop :=

| E_Nat : forall L P pc e n,
(* ------------------------------------------------------ *)
    [L, P] pc; e ⊢ TNat n ⇓ Some (Atom (VNat n) pc)

| E_Var : forall L P pc e n v l,
    atIndex e n = Some (Atom v l) ->
(* ------------------------------------------------------ *)
    [L, P] pc; e ⊢ TVar n ⇓ Some (Atom v (l ⊔ pc))

| E_Abs : forall L P pc e t,
(* ------------------------------------------------------ *)
    [L, P] pc; e ⊢ TLam t ⇓ Some (Atom (VClos e t) pc)

| E_App : forall L P pc e t1 t2 e1' t1' l1 a2 a3,
    [L, P] pc; e ⊢ t1 ⇓ Some (Atom (VClos e1' t1') l1) ->
    [L, P] pc; e ⊢ t2 ⇓ Some a2 ->
    [L, P] l1; a2 :: e1' ⊢ t1' ⇓ Some a3 ->
(* ------------------------------------------------------ *)
    [L, P] pc; e ⊢ TApp t1 t2 ⇓ Some a3

(*| E_App1 : forall L P pc e t1 t2,
    [L, P] pc; e ⊢ t1 ⇓ None ->
(* ------------------------------------------------------ *)
    [L, P] pc; e ⊢ TApp t1 t2 ⇓ None*)

(*| E_App2 : forall L P pc e t1 t2, 
    [L, P] pc; e ⊢ t2 ⇓ None ->
(* ------------------------------------------------------ *)
    [L, P] pc; e ⊢ TApp t1 t2 ⇓ None*)

(*| E_App3 : forall L P pc e t1 t2 e1' t1' l1 a2,
    [L, P] pc; e ⊢ t1 ⇓ Some (Atom (VClos e1' t1') l1) ->
    [L, P] pc; e ⊢ t2 ⇓ Some a2 ->
    [L, P] l1; a2 :: e1' ⊢ t1' ⇓ None ->
(* ------------------------------------------------------ *)
    [L, P] pc; e ⊢ TApp t1 t2 ⇓ None*)

| E_Decl1 : forall L P pc e t1 t2 v,
    [L, P] pc; e ⊢ TApp t1 t2 ⇓ Some (Atom v Bottom2) ->
(* ------------------------------------------------------ *)
    [L, P] pc; e ⊢ TDecl t1 t2 ⇓ Some (Atom v Bottom2)

(*| E_Decl : forall L P pc e t1 t2,
    [L, P] pc; e ⊢ TApp t1 t2 ⇓ None ->
(* ------------------------------------------------------ *)
    [L, P] pc; e ⊢ TDecl t1 t2 ⇓ None*)

| E_Decl2 : forall L P pc e t1 t2 e1' t1' l1 a2 v3,
    [L, P] pc; e ⊢ t1 ⇓ Some (Atom (VClos e1' t1') l1) ->
    [L, P] pc; e ⊢ t2 ⇓ Some a2 ->
    [L, P] l1; a2 :: e1' ⊢ t1' ⇓ Some (Atom v3 Top2) ->
    forall a2' e2' v3',
      env_LPequiv L P (a2 :: e1') (a2' :: e2') ->
      [L, P] l1; a2' :: e2' ⊢ t1' ⇓ Some (Atom v3' Top2) ->
      value_LPequiv L P v3 v3' ->
(* ------------------------------------------------------ *)
    [L, P] pc; e ⊢ TDecl t1 t2 ⇓ Some (Atom v3 Bottom2)

| E_Decl21 : forall L P pc e t1 t2 e1' t1' l1 a2 v3,
    [L, P] pc; e ⊢ t1 ⇓ Some (Atom (VClos e1' t1') l1) ->
    [L, P] pc; e ⊢ t2 ⇓ Some a2 ->
    [L, P] l1; a2 :: e1' ⊢ t1' ⇓ Some (Atom v3 Top2) ->
    forall a2' e2',
      env_LPequiv L P (a2 :: e1') (a2' :: e2') ->
      [L, P] l1; a2' :: e2' ⊢ t1' ⇓ None ->
(* ------------------------------------------------------ *)
    [L, P] pc; e ⊢ TDecl t1 t2 ⇓ Some (Atom v3 Bottom2)

where "[ L , P ] pc ; e ⊢ t ⇓ a" := (eval L P pc e t a).

Hint Constructors eval.

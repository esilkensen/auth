Require Export LambdaTwoSyntax.
Require Export IndistinguishabilityTwo.

Reserved Notation "P , pc ; e ⊢ t ⇓ a" (at level 70).
Inductive eval : (nat -> Prop) -> two -> env -> term -> atom -> Prop :=
| E_Bool : forall P pc e b,
(* ------------------------------------------------ *)
    P, pc; e ⊢ TBool b ⇓ Atom (VBool b) pc
| E_Nat : forall P pc e n,
(* ------------------------------------------------ *)
    P, pc; e ⊢ TNat n ⇓ Atom (VNat n) pc
| E_Var : forall P pc e n v l,
    atIndex e n = Some (Atom v l) ->
(* ------------------------------------------------ *)
    P, pc; e ⊢ TVar n ⇓ Atom v (l ⊔ pc)
| E_Abs : forall P pc e t,
(* ------------------------------------------------ *)
    P, pc; e ⊢ TAbs t ⇓ Atom (VClos e t) pc
| E_App : forall P pc e t1 t2 e1' t1' l1 a2 a3,
    P, pc; e ⊢ t1 ⇓ Atom (VClos e1' t1') l1 ->
    P, pc; e ⊢ t2 ⇓ a2 ->
    P, l1; a2 :: e1' ⊢ t1' ⇓ a3 ->
(* ------------------------------------------------ *)
    P, pc; e ⊢ TApp t1 t2 ⇓ a3
| E_Decl1 : forall P pc e t n L,
    P, pc; e ⊢ t ⇓ Atom (VNat n) L ->
    P n ->
(* ------------------------------------------------ *)
    P, pc; e ⊢ TDecl t ⇓ Atom (VBool true) Bottom2
| E_Decl2 : forall P pc e t n L,
    P, pc; e ⊢ t ⇓ Atom (VNat n) L ->
    ~ P n ->
(* ------------------------------------------------ *)
    P, pc; e ⊢ TDecl t ⇓ Atom (VBool false) Bottom2
where "P , pc ; e ⊢ t ⇓ a" := (eval P pc e t a).

Hint Constructors eval.

Require Export LambdaTwoSyntax.
Require Export IndistinguishabilityTwo.

(** * Its semantics: big step evaluation judgment. *)
Reserved Notation "P , pc ; e ⊢ t ⇓ a" (at level 70).
Inductive eval :
  (value -> value -> Prop) -> two -> env -> term -> atom -> Prop :=
| Eval_nat : forall P pc e n,
(* ------------------------------------- *)
    P, pc; e ⊢ TNat n ⇓ Atom (VNat n) pc
| Eval_var : forall P pc e n v l,
    atIndex e n = Some (Atom v l) ->
(* ---------------------------------- *)
    P, pc; e ⊢ TVar n ⇓ Atom v (l ⊔ pc)
| Eval_lam : forall P pc e t,
(* -------------------------------------- *)
    P, pc; e ⊢ TLam t ⇓ Atom (VClos e t) pc
| Eval_app : forall P pc e t1 t2 e1' t1' l1 a2 a3,
    P, pc; e ⊢ t1 ⇓ Atom (VClos e1' t1') l1 ->
    P, pc; e ⊢ t2 ⇓ a2 ->
    P, l1; a2 :: e1' ⊢ t1' ⇓ a3 ->
(* ----------------------------------------- *)
    P, pc; e ⊢ TApp t1 t2 ⇓ a3
| Eval_decl1 : forall P pc e t1 t2 v,
    P, pc; e ⊢ TApp t1 t2 ⇓ Atom v Bottom2 ->
(* ----------------------------------------- *)
    P, pc; e ⊢ TDecl t1 t2 ⇓ Atom v Bottom2
where "P , pc ; e ⊢ t ⇓ a" := (eval P pc e t a).

Hint Constructors eval.

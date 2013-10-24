Require Export LambdaTwoSyntax.
Require Export IndistinguishabilityTwo.

(** * Its semantics: big step evaluation judgment. *)
Reserved Notation "pc ; e ⊢ t ⇓ a" (at level 70).
Inductive eval : two -> env -> term -> atom -> Prop :=
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
where "pc ; e ⊢ t ⇓ a" := (eval pc e t a).

Hint Constructors eval.

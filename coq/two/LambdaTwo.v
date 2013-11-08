Require Import Arith. 
Require Import Wf_nat.
Require Import LibTactics.

Require Export LambdaTwoSyntax.
Require Export IndistinguishabilityTwo.

Definition eval : nat -> two -> (value -> value -> Prop) ->
                  two -> env -> term -> atom -> Prop.
  refine
    (Fix lt_wf (fun _ => two -> (value -> value -> Prop) ->
                         two -> env -> term -> atom -> Prop)
         (fun (k : nat)
              (eval : forall k' : nat,
                        k' < k -> two -> (value -> value -> Prop) ->
                        two -> env -> term -> atom -> Prop) =>
            fun (L : two) (P : value -> value -> Prop)
                (pc : two) (e : env) (t : term) (a : atom) =>
              match t with
                | TNat n =>
                  a = Atom (VNat n) pc
                | TVar n =>
                  exists v l,
                    atIndex e n = Some (Atom v l) /\
                    a = Atom v (l ⊔ pc)
                | TAbs t' =>
                  a = Atom (VClos e t') pc
                | TApp t1 t2 =>
                  exists k' e1' t1' l1 a2 a3,
                    if lt_dec k' k then
                      eval k' _ L P pc e t1 (Atom (VClos e1' t1') l1) /\
                      eval k' _ L P pc e t2 a2 /\
                      eval k' _ L P l1 (a2 :: e1') t1' a3 /\
                      a = a3
                    else False
                | TDecl t1 t2 =>
                  exists k' e1' t1' l1 a2 v3 l3,
                    if lt_dec k' k then
                      eval k' _ L P pc e t1 (Atom (VClos e1' t1) l1) /\
                      eval k' _ L P pc e t2 a2 /\
                      eval k' _ L P l1 (a2 :: e1') t1' (Atom v3 l3) /\
                      match l3 with
                        | Bottom2 =>
                          a = Atom v3 Bottom2
                        | Top2 =>
                          (* TODO *)
                          (*(forall a2' e2' v3',
                             env_LPequiv L P (a2 :: e1') (a2' :: e2') ->
                             eval k' _ L P l1 (a2' :: e2') t1' (Atom v3' Top2) ->
                             value_LPequiv L P v3 v3') /\*)
                          a = Atom v3 Bottom2
                      end
                    else False
                   end)); auto.
Defined.

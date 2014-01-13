Require Import Program.Tactics.
Require Import MyTactics.
Require Import LabelAlgebra.
Require Import LambdaSyntax.

Section Indistinguishability.

Context (L : Type)
        (M : LabelAlgebra unit L)
        (l : L)
        (P : value L -> value L -> Prop)
        (Prefl : forall v, P v v).

Fixpoint atom_LPequiv a1 a2 : Prop :=
  match a1, a2 with
    | Atom v1 l1, Atom v2 l2 =>
      ((l1 ⊑ l \/ l2 ⊑ l) -> (value_LPequiv v1 v2 /\ l1 =L l2)) /\
      ((l ⊑ l1 /\ l ⊑ l2) ->
       match v1, v2 with
         | VNat n1, VNat n2 => P v1 v2
         | VClos e1 t1, VClos e2 t2 => value_LPequiv v1 v2
         | _, _ => True
       end)
  end
with value_LPequiv v1 v2 : Prop :=
       match v1, v2 with
         | VBool b1, VBool b2 => b1 = b2
         | VNat n1, VNat n2 => n1 = n2
         | VClos e1 t1, VClos e2 t2 =>
           list_forall2 atom_LPequiv e1 e2 /\ t1 = t2
         | VBool _, _ | VNat _, _ | VClos _ _, _ => False
       end.

Definition env_LPequiv : env L -> env L -> Prop :=
  list_forall2 atom_LPequiv.

End Indistinguishability.

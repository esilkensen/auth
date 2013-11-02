Require Export LambdaTwoSyntax.
Require Export IndistinguishabilityTwo.


Fixpoint eval L P pc e t a k {struct k} : Prop :=
  match t, k with
    | TNat n, 0 =>
      a = Atom (VNat n) pc
    | TVar n, 0 =>
      match atIndex e n with
        | Some (Atom v l) =>
          a = Atom v (l ⊔ pc)
        | None => False
      end
    | TLam t', 0 =>
      a = Atom (VClos e t') pc
    | TApp t1 t2, S k' =>
      forall e1' t1' l1 a2 a3,
        eval L P pc e t1 (Atom (VClos e1' t1') l1) k' ->
        eval L P pc e t2 a2 k' ->
        eval L P l1 (a2 :: e1') t1' a3 k' ->
        a = a3
    | TDecl t1 t2, S k' =>
      forall e1' t1' l1 a2 a3,
        eval L P pc e t1 (Atom (VClos e1' t1') l1) k' ->
        eval L P pc e t2 a2 k' ->
        eval L P l1 (a2 :: e1') t1' a3 k' ->
        match a3 with
          | Atom v3 Bottom2 =>
            a = a3
          | Atom v3 Top2 =>
            (forall a2' e2' v3',
               env_LPequiv L P (a2 :: e1') (a2' :: e2') ->
               eval L P l1 (a2' :: e2') t1' (Atom v3' Top2) k' ->
               value_LPequiv L P v3 v3') ->
            a = Atom v3 Bottom2
        end
    | _, _ => False
  end.

Require Export LambdaTwoSyntax.
Require Export IndistinguishabilityTwo.

Fixpoint eval L P pc e t k a {struct k} :=
  match t with
    | TNat n =>
      a = Atom (VNat n) pc
    | TVar n =>
      match atIndex e n with
        | Some (Atom v l) =>
          a = Atom v (l ⊔ pc)
        | None => False
      end
    | TLam t' =>
      a = Atom (VClos e t') pc
    | TApp t1 t2 =>
      match k with
        | S k' =>
          forall e1' t1' l1 a2 a3,
            eval L P pc e t1 k' (Atom (VClos e1' t1') l1) ->
            eval L P pc e t2 k' a2 ->
            eval L P l1 (a2 :: e1') t1' k' a3 ->
            a = a3
        | 0 => False
      end
    | TDecl t1 t2 =>
      match k with
        | S k' =>
          forall e1' t1' l1 a2 v3 l3,
            eval L P pc e t1 k' (Atom (VClos e1' t1') l1) ->
            eval L P pc e t2 k' a2 ->
            eval L P l1 (a2 :: e1') t1' k' (Atom v3 l3) ->
            match l3 with
              | Bottom2 =>
                a = (Atom v3 Bottom2)
              | Top2 =>
                (forall a2' e2' v3',
                   env_LPequiv L P (a2 :: e1') (a2' :: e2') ->
                   eval L P l1 (a2' :: e2') t1' k' (Atom v3' Top2) ->
                   value_LPequiv L P v3 v3') ->
                a = (Atom v3 Bottom2)
            end
        | 0 => False
      end
  end.

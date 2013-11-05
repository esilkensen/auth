Require Export LambdaTwoSyntax.
Require Export IndistinguishabilityTwo.
Require Import LibTactics.

Fixpoint eval (L : two) (P : value -> value -> Prop)
         (pc : two) (e : env) (t : term) (k : nat) (a : atom)
         {struct k} : Prop :=
  match t, k with
    | TNat n, 0 =>
      a = Atom (VNat n) pc
    | TVar n, 0 =>
      match atIndex e n with
        | Some (Atom v l) =>
          a = Atom v (l ⊔ pc)
        | None => False
      end
    | TAbs t', 0 =>
      a = Atom (VClos e t') pc
    | TApp t1 t2, S k' =>
      forall e1' t1' l1 a2 a3,
        eval L P pc e t1 k' (Atom (VClos e1' t1') l1) ->
        eval L P pc e t2 k' a2 ->
        eval L P l1 (a2 :: e1') t1' k' a3 ->
        a = a3
    | TDecl t1 t2, S k' =>
      forall e1' t1' l1 a2 v3 l3,
        eval L P pc e t1 k' (Atom (VClos e1' t1') l1) ->
        eval L P pc e t2 k' a2 ->
        eval L P l1 (a2 :: e1') t1' k' (Atom v3 l3) ->
        match l3 with
          | Bottom2 =>
            a = Atom v3 Bottom2
          | Top2 =>
            (forall a2' e2' v3',
               env_LPequiv L P (a2 :: e1') (a2' :: e2') ->
               eval L P l1 (a2' :: e2') t1' k' (Atom v3' Top2) ->
               value_LPequiv L P v3 v3') ->
            a = Atom v3 Bottom2
        end
    | _, _ => False
  end.

Lemma eval_nat_inv :
  forall L P k pc e n a,
    eval L P pc e (TNat n) k a ->
    a = Atom (VNat n) pc.
Proof.
  introv Heval. destruct k; auto.
Qed.

Lemma eval_var_inv :
  forall L P k pc e n a,
    eval L P pc e (TVar n) k a ->
    exists v l,
      atIndex e n = Some (Atom v l) /\
      a = Atom v (l ⊔ pc).
Proof.
  introv Heval. remember (atIndex e n) as o.
  destruct o as [[v' l'] |]; destruct pc; destruct k;
  unfold eval in Heval; try rewrite <- Heqo in Heval; inversion Heval;
  apply ex_intro with v'; apply ex_intro with l'; auto.
Qed.
               
Lemma eval_abs_inv :
  forall L P k pc e t a,
    eval L P pc e (TAbs t) k a ->
    a = Atom (VClos e t) pc.
Proof.
  introv Heval. destruct k; auto.
Qed.

Lemma eval_app_inv :
  forall L P k' pc e t1 t2 a,
    eval L P pc e (TApp t1 t2) (S k') a ->
    exists e1' t1' l1 a2 a3,
      eval L P pc e t1 k' (Atom (VClos e1' t1') l1) /\
      eval L P pc e t2 k' a2 /\
      eval L P l1 (a2 :: e1') t1' k' a3 /\
      a = a3.
Proof.
  Admitted.

Lemma eval_decl_inv :
  forall L P k' pc e t1 t2 a,
    eval L P pc e (TDecl t1 t2) (S k') a ->
    exists e1' t1' l1 a2 v3 l3,
      eval L P pc e t1 k' (Atom (VClos e1' t1') l1) /\
      eval L P pc e t2 k' a2 /\
      eval L P l1 (a2 :: e1') t1' k' (Atom v3 l3) /\
      (l3 = Bottom2 /\
       a = Atom v3 Bottom2 \/
       l3 = Top2 /\
       (forall a2' e2' v3',
          env_LPequiv L P (a2 :: e1') (a2' :: e2') ->
          eval L P l1 (a2' :: e2') t1' k' (Atom v3' Top2) ->
          value_LPequiv L P v3 v3') /\
       a = Atom v3 Bottom2).
Proof.
  Admitted.

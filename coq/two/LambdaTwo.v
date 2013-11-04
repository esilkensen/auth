Require Export LambdaTwoSyntax.
Require Export IndistinguishabilityTwo.
Require Import LibTactics.

Fixpoint eval (L : two) (P : value -> value -> Prop) (pc : two) (e : env)
         (t : term) (k : nat) (a : atom) {struct k} :=
  match t with
    | TNat n =>
      a = Atom (VNat n) pc
    | TVar n =>
      match atIndex e n with
        | Some (Atom v l) =>
          a = Atom v (l ⊔ pc)
        | None => False
      end
    | TAbs t' =>
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
                a = Atom v3 Bottom2
              | Top2 =>
                (forall a2' e2' v3',
                   env_LPequiv L P (a2 :: e1') (a2' :: e2') ->
                   eval L P l1 (a2' :: e2') t1' k' (Atom v3' Top2) ->
                   value_LPequiv L P v3 v3') ->
                a = Atom v3 Bottom2
            end
        | 0 => False
      end
  end.

Lemma eval_nat_inv :
  forall L P k pc e n a,
    eval L P pc e (TNat n) k a ->
    a = Atom (VNat n) pc.
Proof.
  introv Heval.
  destruct k; auto.
Qed.

Lemma eval_var_inv :
  forall L P k pc e n v l a,
    eval L P pc e (TVar n) k a ->
    a = Atom v l ->
    (l = Bottom2 /\
     atIndex e n = Some (Atom v Bottom2)) \/
    (l = Top2 /\ pc = Top2 /\
     atIndex e n = Some (Atom v Bottom2)) \/
    (l = Top2 /\ pc = Top2 /\
     atIndex e n = Some (Atom v Top2)) \/
    (l = Top2 /\ pc = Bottom2 /\
     atIndex e n = Some (Atom v Top2)).
Proof.
  introv Heval Ha.
  destruct l; destruct pc; subst.
  - destruct k; unfold eval in Heval;
    remember (atIndex e n) as o; destruct o as [[v' l'] |]; subst; auto;
    rewrite join_bot in Heval; inversion Heval;
    left; auto.
  - destruct k; unfold eval in Heval;
    remember (atIndex e n) as o; destruct o as [[v' l'] |]; subst; auto;
    rewrite join_top in Heval; inversion Heval; 
    left; auto.
  - destruct k; unfold eval in Heval;
    remember (atIndex e n) as o; destruct o as [[v' l'] |]; subst; auto;
    rewrite join_bot in Heval; inversion Heval;
    right; right; right; auto.
  - destruct k; unfold eval in Heval;
    remember (atIndex e n) as o; destruct o as [[v' l'] |]; subst; auto;
    inversion Heval; destruct l'.
    + right. left. auto.
    + right. right. left. auto.
    + right. left. auto.
    + right. right. left. auto.
Qed.

Lemma eval_abs_inv :
  forall L P k pc e t a,
    eval L P pc e (TAbs t) k a ->
    a = Atom (VClos e t) pc.
Proof.
  introv Heval.
  destruct k; auto.
Qed.

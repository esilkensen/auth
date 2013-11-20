Require Import Omega.
Require Import Recdef.
Require Export LambdaTwoSyntax.
Require Export IndistinguishabilityTwo.

Definition pair_add (a : nat * nat) : nat :=
  match a with
    | (a1, a2) => a1 + a2
  end.

Definition pair_lt (a b : nat * nat) : Prop :=
  pair_add a < pair_add b.

Lemma pair_lt_wf' :
  forall s a, pair_add a <= s -> Acc pair_lt a.
Proof.
  induction s; intros a H1.
  - destruct a as [a1 a2]; destruct a1; destruct a2; auto.
    apply Acc_intro. intros y H2. inversion H2.
  - inversion H1 as [H2 | n H2 Heq]; auto.
    apply Acc_intro. intros y H3. inversion H3; auto.
Defined.

Theorem pair_lt_wf : well_founded pair_lt.
Proof.
  unfold well_founded; intro; eapply pair_lt_wf'; eauto.
Defined.

Definition eval_kl : nat * nat -> two -> (value -> value -> Prop) ->
                     two -> env -> term -> atom -> Prop.
  refine
    (Fix pair_lt_wf (fun _ => two -> (value -> value -> Prop) ->
                              two -> env -> term -> atom -> Prop)
         (fun (kl : nat * nat)
              (eval_kl : forall kl' : nat * nat,
                           pair_lt kl' kl ->
                           two -> (value -> value -> Prop) ->
                           two -> env -> term -> atom -> Prop) =>
            fun (L : two) (P : value -> value -> Prop)
                (pc : two) (e : env) (t : term) (a : atom) =>
              match t with
                | TBool b =>
                  a = Atom (VBool b) pc
                | TNat n =>
                  a = Atom (VNat n) pc
                | TVar n =>
                  exists v l,
                    atIndex e n = Some (Atom v l) /\
                    a = Atom v (l ⊔ pc)
                | TAbs t' =>
                  a = Atom (VClos e t') pc
                | TApp t1 t2 =>
                  if Compare_dec.zerop (fst kl) then False
                  else exists e1' t1' l1 a2 a3,
                         eval_kl (fst kl - 1, snd kl) _
                                 L P pc e t1 (Atom (VClos e1' t1') l1) /\
                         eval_kl (fst kl - 1, snd kl) _
                                 L P pc e t2 a2 /\
                         eval_kl (fst kl - 1, snd kl) _
                                 L P l1 (a2 :: e1') t1' a3 /\
                         a = a3
                | _ => False
              end)).
  - assert (kl = (fst kl, snd kl)) by
      (destruct kl; auto); rewrite H; simpl; clear H.
    inversion _H; unfold pair_lt; auto.
  - assert (kl = (fst kl, snd kl)) by
      (destruct kl; auto); rewrite H; simpl; clear H.
    inversion _H; unfold pair_lt; auto.
  - assert (kl = (fst kl, snd kl)) by
      (destruct kl; auto); rewrite H; simpl; clear H.
    inversion _H; unfold pair_lt; auto.
Defined.

    (*| TDecl t1 t2 =>
      match kl with
        | (S k', l) =>
          exists e1' t1' l1 a2 v3 l3,
            eval_kl (k', l) L P pc e t1 (Atom (VClos e1' t1') l1) /\
            eval_kl (k', l) L P pc e t2 a2 /\
            eval_kl (k', l) L P l1 (a2 :: e1') t1' (Atom v3 l3) /\
            match l3 with
              | Bottom2 =>
                a = Atom v3 Bottom2
              | Top2 =>
                (forall a2' e2' v3',
                   env_LPequiv L P (a2 :: e1') (a2' :: e2') ->
                   eval_kl (l, k') L P l1 (a2' :: e2') t1' (Atom v3' Top2) ->
                   value_LPequiv L P v3 v3') /\
                a = Atom v3 Bottom2
            end
        | (0, _) => False
      end*)

Definition eval (L : two) (P : value -> value -> Prop)
           (pc : two) (e : env) (t : term) (a : atom) : Prop :=
  exists k, forall l, eval_kl (k, l) L P pc e t a.

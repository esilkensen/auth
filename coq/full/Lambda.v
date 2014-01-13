Require Import FunctionalExtensionality.
Require Import LibTactics.
Require Export LambdaSyntax Indistinguishability.

Lemma functional_extensionality_ex :
  forall {A : Type} (f g : A -> Prop),
    (forall x, f x = g x) ->
    (exists x, f x) = (exists x, g x).
Proof.
  intros. apply functional_extensionality in H. subst. reflexivity.
Qed.

Definition pair_lt (a b : nat * nat) : Prop :=
  fst a + snd a < fst b + snd b.

Lemma pair_lt_wf' :
  forall s a, fst a + snd a <= s -> Acc pair_lt a.
Proof.
  induction s; intros a H1.
  - destruct a as [a1 a2]; destruct a1; destruct a2;
    apply Acc_intro; intros y H2; inversion H1; inversion H2.
  - inversion H1 as [H2 | n H2 Heq]; auto.
    apply Acc_intro. intros y H3. apply IHs. inversion H3; omega.
Defined.

Theorem pair_lt_wf : well_founded pair_lt.
Proof.
  unfold well_founded; intro; eapply pair_lt_wf'; eauto.
Defined.

Definition eval_km {L : Type} {M : LabelAlgebra unit L} :
  nat * nat -> L -> (value L -> value L -> Prop) ->
  L -> env L -> term L -> atom L -> Prop.
  refine
    (Fix pair_lt_wf (fun _ => L -> (value L -> value L -> Prop) ->
                              L -> env L -> term L -> atom L -> Prop)
         (fun km eval_km =>
            fun l P pc e t a =>
              match t with
                | TBool b =>
                  a = Atom (VBool L b) pc
                | TNat n =>
                  a = Atom (VNat L n) pc
                | TVar n =>
                  exists v l,
                    atIndex e n = Some (Atom v l) /\
                    a = Atom v (l ⊔ pc)
                | TAbs t' =>
                  a = Atom (VClos e t') pc
                | TApp t1 t2 =>
                  if Compare_dec.zerop (fst km) then False
                  else let eval := eval_km (fst km - 1, snd km) _ in
                       exists e1' t1' l1 a2,
                         eval l P pc e t1 (Atom (VClos e1' t1') l1) /\
                         eval l P pc e t2 a2 /\
                         eval l P l1 (a2 :: e1') t1' a
                | TRelabel t' l' =>
                  if Compare_dec.zerop (fst km) then False
                  else let eval := eval_km (fst km - 1, snd km) _ in
                       exists v l1,
                         eval l P pc e t' (Atom v l1) /\
                         ((l1 ⊑ l' /\
                           a = Atom v l') \/
                          (l' ⊑ l1 /\
                           let eval := eval_km (snd km, fst km - 1) _ in
                           (forall e' v',
                              env_LPequiv L M l P e e' ->
                              eval l P pc e' t' (Atom v' l1) ->
                              value_LPequiv L M l P v v') /\
                           a = Atom v l'))
              end));
  unfold pair_lt; simpl; omega.
Defined.

Lemma eval_km_eq {L : Type} {M : LabelAlgebra unit L} :
  forall km,
    eval_km km =
    fun l P pc e t a =>
      match t with
        | TBool b =>
          a = Atom (VBool L b) pc
        | TNat n =>
          a = Atom (VNat L n) pc
        | TVar n =>
          exists v l,
            atIndex e n = Some (Atom v l) /\
            a = Atom v (l ⊔ pc)
        | TAbs t' =>
          a = Atom (VClos e t') pc
        | TApp t1 t2 =>
          if Compare_dec.zerop (fst km) then False
          else let eval := eval_km (fst km - 1, snd km) in
               exists e1' t1' l1 a2,
                 eval l P pc e t1 (Atom (VClos e1' t1') l1) /\
                 eval l P pc e t2 a2 /\
                 eval l P l1 (a2 :: e1') t1' a
        | TRelabel t' l' =>
          if Compare_dec.zerop (fst km) then False
          else let eval := eval_km (fst km - 1, snd km) in
               exists v l1,
                 eval l P pc e t' (Atom v l1) /\
                 ((l1 ⊑ l' /\
                   a = Atom v l') \/
                  (l' ⊑ l1 /\
                   let eval := eval_km (snd km, fst km - 1) in
                   (forall e' v',
                      env_LPequiv L M l P e e' ->
                      eval l P pc e' t' (Atom v' l1) ->
                      value_LPequiv L M l P v v') /\
                   a = Atom v l'))
      end.
Proof.
  intro km.
  apply (Fix_eq pair_lt_wf (fun _ => L -> (value L -> value L -> Prop) ->
                                     L -> env L -> term L -> atom L -> Prop));
    intros; destruct x as [x1 x2].
  apply functional_extensionality; intro l.
  apply functional_extensionality; intro P.
  apply functional_extensionality; intro pc.
  apply functional_extensionality; intro e.
  apply functional_extensionality; intro t.
  apply functional_extensionality; intro a.
  destruct t; try reflexivity;
  assert (H': forall (y : nat * nat), f y = g y) by
      (intro; apply functional_extensionality; apply H).
  - destruct x1; auto; simpl.
    apply functional_extensionality_ex; intro e1'.
    apply functional_extensionality_ex; intro t1'.
    apply functional_extensionality_ex; intro l1.
    apply functional_extensionality_ex; intro a2.
    rewrite H'. reflexivity.
  - destruct x1; auto; simpl.
    apply functional_extensionality_ex; intro v.
    apply functional_extensionality_ex; intro l1.
    rewrite 2! H'. reflexivity.
Qed.

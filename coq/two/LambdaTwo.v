Require Import FunctionalExtensionality.
Require Import LibTactics.
Require Export LambdaTwoSyntax IndistinguishabilityTwo.

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

Definition eval_kl : nat * nat -> two -> (value -> value -> Prop) ->
                     two -> env -> term -> atom -> Prop.
  refine
    (Fix pair_lt_wf (fun _ => two -> (value -> value -> Prop) ->
                              two -> env -> term -> atom -> Prop)
         (fun kl eval_kl =>
            fun L P pc e t a =>
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
                  else let eval := eval_kl (fst kl - 1, snd kl) _ in
                       exists e1' t1' l1 a2,
                         eval L P pc e t1 (Atom (VClos e1' t1') l1) /\
                         eval L P pc e t2 a2 /\
                         eval L P l1 (a2 :: e1') t1' a
                | TDecl t' =>
                  if Compare_dec.zerop (fst kl) then False
                  else let eval := eval_kl (fst kl - 1, snd kl) _ in
                       exists v l1,
                         eval L P pc e t' (Atom v l1) /\
                         if bottomp l1 then a = Atom v Bottom2
                         else let eval := eval_kl (snd kl, fst kl - 1) _ in
                              (forall e' v',
                                 env_LPequiv L P e e' ->
                                 eval L P pc e' t' (Atom v' Top2) ->
                                 value_LPequiv L P v v') /\
                              a = Atom v Bottom2
              end));
  unfold pair_lt; simpl; omega.
Defined.

Lemma eval_kl_eq :
  forall kl,
    eval_kl kl =
    fun L P pc e t a =>
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
          else let eval := eval_kl (fst kl - 1, snd kl) in
               exists e1' t1' l1 a2,
                 eval L P pc e t1 (Atom (VClos e1' t1') l1) /\
                 eval L P pc e t2 a2 /\
                 eval L P l1 (a2 :: e1') t1' a
        | TDecl t' =>
          if Compare_dec.zerop (fst kl) then False
          else let eval := eval_kl (fst kl - 1, snd kl) in
               exists v l1,
                 eval L P pc e t' (Atom v l1) /\
                 if bottomp l1 then a = Atom v Bottom2
                 else let eval := eval_kl (snd kl, fst kl - 1) in
                      (forall e' v',
                         env_LPequiv L P e e' ->
                         eval L P pc e' t' (Atom v' Top2) ->
                         value_LPequiv L P v v') /\
                      a = Atom v Bottom2
      end.
Proof.
  intro kl.
  apply (Fix_eq pair_lt_wf (fun _ => two -> (value -> value -> Prop) ->
                                     two -> env -> term -> atom -> Prop));
    intros; destruct x as [x1 x2].
  apply functional_extensionality; intro L.
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
    destruct l1; rewrite H'; simpl; try rewrite H'; reflexivity.
Qed.

Lemma eval_kl_bool :
  forall k l L P pc e b,
    eval_kl (k, l) L P pc e (TBool b) (Atom (VBool b) pc).
Proof. intros. rewrite eval_kl_eq. auto. Qed.

Lemma eval_kl_bool_inv :
  forall k l L P pc e b a,
    eval_kl (k, l) L P pc e (TBool b) a -> a = Atom (VBool b) pc.
Proof. intros. rewrite eval_kl_eq in H. auto. Qed.

Lemma eval_kl_nat :
  forall k l L P pc e n,
    eval_kl (k, l) L P pc e (TNat n) (Atom (VNat n) pc).
Proof. intros. rewrite eval_kl_eq. auto. Qed.

Lemma eval_kl_nat_inv :
  forall k l L P pc e n a,
    eval_kl (k, l) L P pc e (TNat n) a -> a = Atom (VNat n) pc.
Proof. intros. rewrite eval_kl_eq in H. auto. Qed.

Lemma eval_kl_var :
  forall k l L P pc e n v' l',
    atIndex e n = Some (Atom v' l') ->
    eval_kl (k, l) L P pc e (TVar n) (Atom v' (l' ⊔ pc)).
Proof. intros. rewrite eval_kl_eq. exists v' l'. auto. Qed.

Lemma eval_kl_var_inv :
  forall k l L P pc e n a,
    eval_kl (k, l) L P pc e (TVar n) a ->
    exists v' l',
      atIndex e n = Some (Atom v' l') /\
      a = Atom v' (l' ⊔ pc).
Proof. intros. rewrite eval_kl_eq in H. auto. Qed.

Lemma eval_kl_abs :
  forall k l L P pc e t',
    eval_kl (k, l) L P pc e (TAbs t') (Atom (VClos e t') pc).
Proof. intros. rewrite eval_kl_eq. auto. Qed.

Lemma eval_kl_abs_inv :
  forall k l L P pc e t a,
    eval_kl (k, l) L P pc e (TAbs t) a -> a = Atom (VClos e t) pc.
Proof. intros. rewrite eval_kl_eq in H. auto. Qed.

Lemma eval_kl_app :
  forall k l L P pc e t1 t2 e1' t1' l1 a2 a3,
    eval_kl (k, l) L P pc e t1 (Atom (VClos e1' t1') l1) ->
    eval_kl (k, l) L P pc e t2 a2 ->
    eval_kl (k, l) L P l1 (a2 :: e1') t1' a3 ->
    eval_kl (S k, l) L P pc e (TApp t1 t2) a3.
Proof.
  intros.
  rewrite eval_kl_eq. simpl.
  replace (k - 0) with k by omega.
  exists e1' t1' l1 a2. auto.
Qed.

Lemma eval_kl_app_inv :
  forall k l L P pc e t1 t2 a,
    eval_kl (k, l) L P pc e (TApp t1 t2) a ->
    exists k' e1' t1' l1 a2,
      k = S k' /\
      eval_kl (k', l) L P pc e t1 (Atom (VClos e1' t1') l1) /\
      eval_kl (k', l) L P pc e t2 a2 /\
      eval_kl (k', l) L P l1 (a2 :: e1') t1' a.
Proof.
  intros.
  rewrite eval_kl_eq in H.
  destruct k; simpl in H.
  - inversion H.
  - destruct H as [e1' [t1' [l1 [a2 [H1 [H2 H3]]]]]].
    replace (k - 0) with k in * by omega.
    exists k e1' t1' l1 a2. auto.
Qed.

Lemma eval_kl_decl1 :
  forall k l L P pc e t v,
    eval_kl (k, l) L P pc e t (Atom v Bottom2) ->
    eval_kl (S k, l) L P pc e (TDecl t) (Atom v Bottom2).
Proof.
  intros.
  rewrite eval_kl_eq. simpl.
  replace (k - 0) with k by omega.
  exists v Bottom2. simpl. auto.
Qed.

Lemma eval_kl_decl2 :
  forall k l L P pc e t v,
    eval_kl (k, l) L P pc e t (Atom v Top2) ->
    (forall e' v',
       env_LPequiv L P e e' ->
       eval_kl (l, k) L P pc e' t (Atom v' Top2) ->
       value_LPequiv L P v v') ->
    eval_kl (S k, l) L P pc e (TDecl t) (Atom v Bottom2).
Proof.
  intros.
  rewrite eval_kl_eq. simpl.
  replace (k - 0) with k by omega.
  exists v Top2. simpl. auto.
Qed.

Lemma eval_kl_decl_inv :
  forall k l L P pc e t a,
    eval_kl (k, l) L P pc e (TDecl t) a ->
    (exists k' v,
       k = S k' /\
       eval_kl (k', l) L P pc e t (Atom v Bottom2) /\
       a = Atom v Bottom2) \/
    (exists k' v,
       k = S k' /\
       eval_kl (k', l) L P pc e t (Atom v Top2) /\
       (forall e' v',
          env_LPequiv L P e e' ->
          eval_kl (l, k') L P pc e' t (Atom v' Top2) ->
          value_LPequiv L P v v') /\
       a = Atom v Bottom2).
Proof.
  intros.
  rewrite eval_kl_eq in H.
  destruct k; simpl in H.
  - inversion H.
  - destruct H as [v [l1 [H1 H2]]].
    replace (k - 0) with k in * by omega.
    destruct l1; simpl in H2.
    + left. exists k v. auto.
    + right. exists k v. auto.
Qed.

Definition eval (L : two) (P : value -> value -> Prop)
           (pc : two) (e : env) (t : term) (a : atom) : Prop :=
  exists k, forall l, eval_kl (k, l) L P pc e t a.

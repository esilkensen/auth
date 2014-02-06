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
                    a = Atom v l
                | TAbs t' =>
                  a = Atom (VClos e t') pc
                | TApp t1 t2 =>
                  if Compare_dec.zerop (fst km) then False
                  else let eval := eval_km (fst km - 1, snd km) _ in
                       exists e1' t1' l1 a2,
                         eval l P pc e t1 (Atom (VClos e1' t1') l1) /\
                         eval l P pc e t2 a2 /\
                         eval l P l1 (a2 :: e1') t1' a
                | TPrim f t1 t2 =>
                  if Compare_dec.zerop (fst km) then False
                  else let eval := eval_km (fst km - 1, snd km) _ in
                       exists n1 l1 n2 l2,
                         eval l P pc e t1 (Atom (VNat L n1) l1) /\
                         eval l P pc e t2 (Atom (VNat L n2) l2) /\
                         (forall n1' n2',
                            P (VNat L n1) (VNat L n1') ->
                            P (VNat L n2) (VNat L n2') ->
                            P (VNat L (f n1 n2)) (VNat L (f n1' n2'))) /\
                         a = Atom (VNat L (f n1 n2)) (l1 ⊔ l2)
                | TRelabel t' l' =>
                  if Compare_dec.zerop (fst km) then False
                  else let eval := eval_km (fst km - 1, snd km) _ in
                       exists v l1,
                         eval l P pc e t' (Atom v l1) /\
                         ((l1 ⊑ l' /\
                           a = Atom v l') \/
                          (l' ⊑ l1 /\
                           let eval := eval_km (snd km, fst km - 1) _ in
                           (forall pc' e' v' l1',
                              lab_Lequiv L M l pc pc' ->
                              env_LPequiv L M l P e e' ->
                              lab_Lequiv L M l l1 l1' ->
                              eval l P pc' e' t' (Atom v' l1') ->
                              value_LPequiv L M l P v v') /\
                           a = Atom v l'))
                | TIf t1 t2 t3 =>
                  if Compare_dec.zerop (fst km) then False
                  else let eval := eval_km (fst km - 1, snd km) _ in
                       exists b l1,
                         eval l P pc e t1 (Atom (VBool L b) l1) /\
                         l1 ⊑ l /\
                         if b then eval l P (l1 ⊔ pc) e t2 a
                         else eval l P (l1 ⊔ pc) e t3 a
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
            a = Atom v l
        | TAbs t' =>
          a = Atom (VClos e t') pc
        | TApp t1 t2 =>
          if Compare_dec.zerop (fst km) then False
          else let eval := eval_km (fst km - 1, snd km) in
               exists e1' t1' l1 a2,
                 eval l P pc e t1 (Atom (VClos e1' t1') l1) /\
                 eval l P pc e t2 a2 /\
                 eval l P l1 (a2 :: e1') t1' a
        | TPrim f t1 t2 =>
          if Compare_dec.zerop (fst km) then False
          else let eval := eval_km (fst km - 1, snd km) in
               exists n1 l1 n2 l2,
                 eval l P pc e t1 (Atom (VNat L n1) l1) /\
                 eval l P pc e t2 (Atom (VNat L n2) l2) /\
                 (forall n1' n2',
                    P (VNat L n1) (VNat L n1') ->
                    P (VNat L n2) (VNat L n2') ->
                    P (VNat L (f n1 n2)) (VNat L (f n1' n2'))) /\
                 a = Atom (VNat L (f n1 n2)) (l1 ⊔ l2)
        | TRelabel t' l' =>
          if Compare_dec.zerop (fst km) then False
          else let eval := eval_km (fst km - 1, snd km) in
               exists v l1,
                 eval l P pc e t' (Atom v l1) /\
                 ((l1 ⊑ l' /\
                   a = Atom v l') \/
                  (l' ⊑ l1 /\
                   let eval := eval_km (snd km, fst km - 1) in
                   (forall pc' e' v' l1',
                      lab_Lequiv L M l pc pc' ->
                      env_LPequiv L M l P e e' ->
                      lab_Lequiv L M l l1 l1' ->
                      eval l P pc' e' t' (Atom v' l1') ->
                      value_LPequiv L M l P v v') /\
                   a = Atom v l'))
        | TIf t1 t2 t3 =>
          if Compare_dec.zerop (fst km) then False
          else let eval := eval_km (fst km - 1, snd km) in
               exists b l1,
                 eval l P pc e t1 (Atom (VBool L b) l1) /\
                 l1 ⊑ l /\
                 if b then eval l P (l1 ⊔ pc) e t2 a
                 else eval l P (l1 ⊔ pc) e t3 a
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
      (intro; apply functional_extensionality; apply H);
  destruct x1; auto; simpl.
  - apply functional_extensionality_ex; intro e1'.
    apply functional_extensionality_ex; intro t1'.
    apply functional_extensionality_ex; intro l1.
    apply functional_extensionality_ex; intro a2.
    rewrite H'. reflexivity.
  - apply functional_extensionality_ex; intro n1.
    apply functional_extensionality_ex; intro l1.
    apply functional_extensionality_ex; intro n2.
    apply functional_extensionality_ex; intro l2.
    rewrite H'. reflexivity.
  - apply functional_extensionality_ex; intro v.
    apply functional_extensionality_ex; intro l1.
    rewrite 2! H'. reflexivity.
  - apply functional_extensionality_ex; intro b.
    apply functional_extensionality_ex; intro l1.
    rewrite H'. reflexivity.
Qed.

Lemma eval_km_bool {L : Type} {M : LabelAlgebra unit L} :
  forall k m l P pc e b,
    eval_km (k, m) l P pc e (TBool L b) (Atom (VBool L b) pc).
Proof. intros. rewrite eval_km_eq. auto. Qed.

Lemma eval_km_bool_inv {L : Type} {M : LabelAlgebra unit L} :
  forall k m l P pc e b a,
    eval_km (k, m) l P pc e (TBool L b) a -> a = Atom (VBool L b) pc.
Proof. intros. rewrite eval_km_eq in H. auto. Qed.

Lemma eval_km_nat {L : Type} {M : LabelAlgebra unit L} :
  forall k m l P pc e n,
    eval_km (k, m) l P pc e (TNat L n) (Atom (VNat L n) pc).
Proof. intros. rewrite eval_km_eq. auto. Qed.

Lemma eval_km_nat_inv {L : Type} {M : LabelAlgebra unit L} :
  forall k m l P pc e n a,
    eval_km (k, m) l P pc e (TNat L n) a -> a = Atom (VNat L n) pc.
Proof. intros. rewrite eval_km_eq in H. auto. Qed.

Lemma eval_km_var {L : Type} {M : LabelAlgebra unit L} :
  forall k m l P pc e n v' l',
    atIndex e n = Some (Atom v' l') ->
    eval_km (k, m) l P pc e (TVar L n) (Atom v' l').
Proof. intros. rewrite eval_km_eq. exists v' l'. auto. Qed.

Lemma eval_km_var_inv {L : Type} {M : LabelAlgebra unit L} :
  forall k m l P pc e n a,
    eval_km (k, m) l P pc e (TVar L n) a ->
    exists v' l',
      atIndex e n = Some (Atom v' l') /\
      a = Atom v' l'.
Proof. intros. rewrite eval_km_eq in H. auto. Qed.

Lemma eval_km_abs {L : Type} {M : LabelAlgebra unit L} :
  forall k m l P pc e t',
    eval_km (k, m) l P pc e (TAbs t') (Atom (VClos e t') pc).
Proof. intros. rewrite eval_km_eq. auto. Qed.

Lemma eval_km_abs_inv {L : Type} {M : LabelAlgebra unit L} :
  forall k m l P pc e t a,
    eval_km (k, m) l P pc e (TAbs t) a -> a = Atom (VClos e t) pc.
Proof. intros. rewrite eval_km_eq in H. auto. Qed.

Lemma eval_km_app {L : Type} {M : LabelAlgebra unit L} :
  forall k m l P pc e t1 t2 e1' t1' l1 a2 a3,
    eval_km (k, m) l P pc e t1 (Atom (VClos e1' t1') l1) ->
    eval_km (k, m) l P pc e t2 a2 ->
    eval_km (k, m) l P l1 (a2 :: e1') t1' a3 ->
    eval_km (S k, m) l P pc e (TApp t1 t2) a3.
Proof.
  intros.
  rewrite eval_km_eq. simpl.
  replace (k - 0) with k by omega.
  exists e1' t1' l1 a2. auto.
Qed.

Lemma eval_km_app_inv {L : Type} {M : LabelAlgebra unit L} :
  forall k m l P pc e t1 t2 a,
    eval_km (k, m) l P pc e (TApp t1 t2) a ->
    exists k' e1' t1' l1 a2,
      k = S k' /\
      eval_km (k', m) l P pc e t1 (Atom (VClos e1' t1') l1) /\
      eval_km (k', m) l P pc e t2 a2 /\
      eval_km (k', m) l P l1 (a2 :: e1') t1' a.
Proof.
  intros.
  rewrite eval_km_eq in H.
  destruct k; simpl in H.
  - inversion H.
  - destruct H as [e1' [t1' [l1 [a2 [H1 [H2 H3]]]]]].
    replace (k - 0) with k in * by omega.
    exists k e1' t1' l1 a2. auto.
Qed.

Lemma eval_km_prim {L : Type} {M : LabelAlgebra unit L} :
  forall k m l P pc e f t1 t2 n1 l1 n2 l2,
    eval_km (k, m) l P pc e t1 (Atom (VNat L n1) l1) ->
    eval_km (k, m) l P pc e t2 (Atom (VNat L n2) l2) ->
    (forall n1' n2',
       P (VNat L n1) (VNat L n1') ->
       P (VNat L n2) (VNat L n2') ->
       P (VNat L (f n1 n2)) (VNat L (f n1' n2'))) ->
    eval_km (S k, m) l P pc e (TPrim f t1 t2)
            (Atom (VNat L (f n1 n2)) (l1 ⊔ l2)).
Proof.
  intros.
  rewrite eval_km_eq. simpl.
  replace (k - 0) with k by omega.
  exists n1 l1 n2 l2. auto.
Qed.

Lemma eval_km_prim_inv {L : Type} {M : LabelAlgebra unit L} :
  forall k m l P pc e f t1 t2 a,
    eval_km (k, m) l P pc e (TPrim f t1 t2) a ->
    exists k' n1 l1 n2 l2,
      k = S k' /\
      eval_km (k', m) l P pc e t1 (Atom (VNat L n1) l1) /\
      eval_km (k', m) l P pc e t2 (Atom (VNat L n2) l2) /\
      (forall n1' n2',
         P (VNat L n1) (VNat L n1') ->
         P (VNat L n2) (VNat L n2') ->
         P (VNat L (f n1 n2)) (VNat L (f n1' n2'))) /\
      a = Atom (VNat L (f n1 n2)) (l1 ⊔ l2).
Proof.
  intros.
  rewrite eval_km_eq in H.
  destruct k; simpl in H.
  - inversion H.
  - destruct H as [n1 [l1 [n2 [l2 [H1 [H2 [H3 H4]]]]]]].
    replace (k - 0) with k in * by omega.
    exists k n1 l1 n2 l2. auto.
Qed.

Lemma eval_km_relabel_up {L : Type} {M : LabelAlgebra unit L} :
  forall k m l P pc e t' l' v l1,
    eval_km (k, m) l P pc e t' (Atom v l1) ->
    l1 ⊑ l' ->
    eval_km (S k, m) l P pc e (TRelabel t' l') (Atom v l').
Proof.
  intros.
  rewrite eval_km_eq. simpl.
  replace (k - 0) with k by omega.
  exists v l1. auto.
Qed.

Lemma eval_km_relabel_down {L : Type} {M : LabelAlgebra unit L} :
  forall k m l P pc e t' l' v l1,
    eval_km (k, m) l P pc e t' (Atom v l1) ->
    l' ⊑ l1 ->
    (forall pc' e' v' l1',
       lab_Lequiv L M l pc pc' ->
       env_LPequiv L M l P e e' ->
       lab_Lequiv L M l l1 l1' ->
       eval_km (m, k) l P pc' e' t' (Atom v' l1') ->
       value_LPequiv L M l P v v') ->
    eval_km (S k, m) l P pc e (TRelabel t' l') (Atom v l').
Proof.
  intros.
  rewrite eval_km_eq. simpl.
  replace (k - 0) with k by omega.
  exists v l1. auto.
Qed.

Lemma eval_km_relabel_inv {L : Type} {M : LabelAlgebra unit L} :
  forall k m l P pc e t' l' a,
    eval_km (k, m) l P pc e (TRelabel t' l') a ->
    (exists k' v l1,
       k = S k' /\
       eval_km (k', m) l P pc e t' (Atom v l1) /\
       l1 ⊑ l' /\
       a = Atom v l') \/
    (exists k' v l1,
       k = S k' /\
       eval_km (k', m) l P pc e t' (Atom v l1) /\
       l' ⊑ l1 /\
       (forall pc' e' v' l1',
          lab_Lequiv L M l pc pc' ->
          env_LPequiv L M l P e e' ->
          lab_Lequiv L M l l1 l1' ->
          eval_km (m, k') l P pc' e' t' (Atom v' l1') ->
          value_LPequiv L M l P v v') /\
       a = Atom v l').
Proof.
  intros.
  rewrite eval_km_eq in H.
  destruct k; simpl in H.
  - inversion H.
  - destruct H as [v [l1 [H1 H2]]].
    replace (k - 0) with k in * by omega.
    destruct H2 as [[H2 H3] | [H2 H3]].
    + left. exists k v l1. auto.
    + right. exists k v l1. auto.
Qed.

Lemma eval_km_iftrue {L : Type} {M : LabelAlgebra unit L} :
  forall k m l P pc e t1 t2 t3 l1 a,
    eval_km (k, m) l P pc e t1 (Atom (VBool L true) l1) ->
    l1 ⊑ l ->
    eval_km (k, m) l P (l1 ⊔ pc) e t2 a ->
    eval_km (S k, m) l P pc e (TIf t1 t2 t3) a.
Proof.
  introv Ht1 Hl1 Ht2.
  rewrite eval_km_eq. simpl.
  replace (k - 0) with k by omega.
  exists true l1. auto.
Qed.

Lemma eval_km_iffalse {L : Type} {M : LabelAlgebra unit L} :
  forall k m l P pc e t1 t2 t3 l1 a,
    eval_km (k, m) l P pc e t1 (Atom (VBool L false) l1) ->
    l1 ⊑ l ->
    eval_km (k, m) l P (l1 ⊔ pc) e t3 a ->
    eval_km (S k, m) l P pc e (TIf t1 t2 t3) a.
Proof.
  introv Ht1 Hl1 Ht3.
  rewrite eval_km_eq. simpl.
  replace (k - 0) with k by omega.
  exists false l1. auto.
Qed.

Lemma eval_km_if_inv {L : Type} {M : LabelAlgebra unit L} :
  forall k m l P pc e t1 t2 t3 a,
    eval_km (k, m) l P pc e (TIf t1 t2 t3) a ->
    (exists k' l1,
       k = S k' /\
       eval_km (k', m) l P pc e t1 (Atom (VBool L true) l1) /\
       l1 ⊑ l /\
       eval_km (k', m) l P (l1 ⊔ pc) e t2 a) \/
    (exists k' l1,
       k = S k' /\
       eval_km (k', m) l P pc e t1 (Atom (VBool L false) l1) /\
       l1 ⊑ l /\
       eval_km (k', m) l P (l1 ⊔ pc) e t3 a).
Proof.
  intros.
  rewrite eval_km_eq in H.
  destruct k; simpl in H.
  - inversion H.
  - destruct H as [b [l1 [H1 [H2 H3]]]].
    replace (k - 0) with k in * by omega.
    destruct b.
    + left. exists k l1. auto.
    + right. exists k l1. auto.
Qed.

Definition eval {L : Type} {M : LabelAlgebra unit L}
           (l : L) (P : value L -> value L -> Prop)
           (pc : L) (e : env L) (t : term L) (a : atom L) : Prop :=
  exists k, forall m, eval_km (k, m) l P pc e t a.

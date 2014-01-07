Require Import Arith FunctionalExtensionality List Omega.

Require Export LabelAlgebra Two.

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

Inductive term : Type :=
  | TBool : bool -> term
  | TNat : nat -> term
  | TVar : nat -> term
  | TAbs : term -> term
  | TApp : term -> term -> term
  | TDecl : term -> term -> term.

Inductive atom : Type :=
  | Atom : value -> two -> atom
with value : Type :=
     | VBool : bool -> value
     | VNat : nat -> value
     | VClos : list atom -> term -> value.

Definition env : Type := list atom.

Fixpoint lookup (e : env) (n : nat) : option atom :=
  match e with
    | nil => None
    | a :: e' =>
      match n with
        | 0 => Some a
        | S n' => lookup e' n'
      end
  end.

Section Indistinguishability.

  Require Import Program.Tactics.
  Require Import MyList.
  
  Context (L : two)
          (P : value -> value -> Prop)
          (Prefl : forall x, P x x).
  
  Fixpoint atom_LPequiv a1 a2 : Prop :=
    match a1, a2 with
      | Atom v1 l1, Atom v2 l2 =>
        (L = Bottom2 /\ l1 = l2 /\ l1 = Top2 /\
         match v1, v2 with
           | VNat n1, VNat n2 => P v1 v2
           | VClos e1 t1, VClos e2 t2 => value_LPequiv v1 v2
           | _, _ => True
         end) \/
        (L = Bottom2 /\ l1 = l2 /\ l1 = Bottom2 /\ value_LPequiv v1 v2) \/
        (L = Top2 /\ l1 = l2 /\ value_LPequiv v1 v2)
    end
  with value_LPequiv v1 v2 : Prop :=
         match v1, v2 with
           | VBool b1, VBool b2 => b1 = b2
           | VNat n1, VNat n2 => n1 = n2
           | VClos e1 t1, VClos e2 t2 =>
             list_forall2 atom_LPequiv e1 e2 /\ t1 = t2
           | VBool _, _ | VNat _, _ | VClos _ _, _ => False
         end.

  Definition env_LPequiv : env -> env -> Prop :=
    list_forall2 atom_LPequiv.

  Lemma atom_LPequiv_lab_inv :
    forall v1 v2 l1 l2,
      atom_LPequiv (Atom v1 l1) (Atom v2 l2) ->
      l1 = l2.
  Proof.
    intros. inversion H; inversion H0; destruct_conjs; auto.
  Qed.

  Lemma atom_LPequiv_raise :
    forall v1 v2,
      atom_LPequiv (Atom v1 Bottom2) (Atom v2 Bottom2) ->
      atom_LPequiv (Atom v1 Top2) (Atom v2 Top2).
  Proof.
    intros v1 v2 H. destruct L.
    - destruct v1; destruct v2; destruct H; destruct H; destruct_conjs;
      inversion H; try inversion H1; subst; auto.
      + destruct H2. left. auto.
      + right. right. auto.
      + destruct H2. left. auto.
      + right. right. auto.
      + left. auto.
      + right. right. auto.
    - destruct v1; destruct v2; destruct H; destruct H; destruct_conjs;
      inversion H; inversion H1; inversion H2; subst.
      + destruct H2. left. auto.
      + right. right. auto.
      + left. auto.
      + right. right. auto.
      + left. auto.
      + right. right.  auto.
  Qed.

End Indistinguishability.

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
                    lookup e n = Some (Atom v l) /\
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
                | TDecl t1 t2 =>
                  if Compare_dec.zerop (fst kl) then False
                  else let eval := eval_kl (fst kl - 1, snd kl) _ in
                       exists e1' t1' l1 a2 v3 l3,
                         eval L P pc e t1 (Atom (VClos e1' t1') l1) /\
                         eval L P pc e t2 a2 /\
                         eval L P l1 (a2 :: e1') t1' (Atom v3 l3) /\
                         if bottomp l3 then a = Atom v3 Bottom2
                         else let eval := eval_kl (snd kl, fst kl - 1) _ in
                              (forall a2' e2' v3',
                                 env_LPequiv L P (a2 :: e1') (a2' :: e2') ->
                                 eval L P l1 (a2' :: e2') t1' (Atom v3' Top2) ->
                                 value_LPequiv L P v3 v3') /\
                              a = Atom v3 Bottom2
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
            lookup e n = Some (Atom v l) /\
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
        | TDecl t1 t2 =>
          if Compare_dec.zerop (fst kl) then False
          else let eval := eval_kl (fst kl - 1, snd kl) in
               exists e1' t1' l1 a2 v3 l3,
                 eval L P pc e t1 (Atom (VClos e1' t1') l1) /\
                 eval L P pc e t2 a2 /\
                 eval L P l1 (a2 :: e1') t1' (Atom v3 l3) /\
                 if bottomp l3 then a = Atom v3 Bottom2
                 else let eval := eval_kl (snd kl, fst kl - 1) in
                      (forall a2' e2' v3',
                         env_LPequiv L P (a2 :: e1') (a2' :: e2') ->
                         eval L P l1 (a2' :: e2') t1' (Atom v3' Top2) ->
                         value_LPequiv L P v3 v3') /\
                      a = Atom v3 Bottom2
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
    apply functional_extensionality_ex; intro e1'.
    apply functional_extensionality_ex; intro t1'.
    apply functional_extensionality_ex; intro l1.
    apply functional_extensionality_ex; intro a2.
    apply functional_extensionality_ex; intro v3.
    apply functional_extensionality_ex; intro l3.
    destruct l3; rewrite H'; simpl; try rewrite H'; reflexivity.
Qed.

Lemma eval_k_bool :
  forall k l L P pc e b,
    eval_kl (k, l) L P pc e (TBool b) (Atom (VBool b) pc).
Proof. intros. rewrite eval_kl_eq. reflexivity. Qed.

Lemma eval_kl_bool_inv :
  forall k l L P pc e b a,
    eval_kl (k, l) L P pc e (TBool b) a -> a = Atom (VBool b) pc.
Proof. intros. destruct a; destruct k; destruct l; auto. Qed.

Lemma eval_kl_nat :
  forall k l L P pc e n,
    eval_kl (k, l) L P pc e (TNat n) (Atom (VNat n) pc).
Proof. intros. rewrite eval_kl_eq. reflexivity. Qed.

Lemma eval_kl_nat_inv :
  forall k l L P pc e n a,
    eval_kl (k, l) L P pc e (TNat n) a -> a = Atom (VNat n) pc.
Proof. intros. destruct a; destruct k; destruct l; auto. Qed.

Lemma eval_kl_var :
  forall k l L P pc e n v' l',
    lookup e n = Some (Atom v' l') ->
    eval_kl (k, l) L P pc e (TVar n) (Atom v' (l' ⊔ pc)).
Proof. intros. rewrite eval_kl_eq. exists v'. exists l'. auto. Qed.

Lemma eval_kl_var_inv :
  forall k l L P pc e n a,
    eval_kl (k, l) L P pc e (TVar n) a ->
    exists v' l',
      lookup e n = Some (Atom v' l') /\
      a = Atom v' (l' ⊔ pc).
Proof. intros. destruct a; destruct k; destruct l; auto. Qed.

Lemma eval_kl_abs :
  forall k l L P pc e t',
    eval_kl (k, l) L P pc e (TAbs t') (Atom (VClos e t') pc).
Proof. intros. rewrite eval_kl_eq. reflexivity. Qed.

Lemma eval_kl_abs_inv :
  forall k l L P pc e t a,
    eval_kl (k, l) L P pc e (TAbs t) a -> a = Atom (VClos e t) pc.
Proof. intros. destruct a; destruct k; destruct l; auto. Qed.

Lemma eval_kl_app :
  forall k l L P pc e t1 t2 e1' t1' l1 a2 a3,
    eval_kl (k, l) L P pc e t1 (Atom (VClos e1' t1') l1) ->
    eval_kl (k, l) L P pc e t2 a2 ->
    eval_kl (k, l) L P l1 (a2 :: e1') t1' a3 ->
    eval_kl (S k, l) L P pc e (TApp t1 t2) a3.
Proof.
  intros. rewrite eval_kl_eq. simpl.
  replace (k - 0) with k by omega.
  exists e1'. exists t1'. exists l1. exists a2.
  split; try split; assumption.
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
    exists k. exists e1'. exists t1'. exists l1. exists a2.
    split; try split; try split; assumption.
Qed.

Lemma eval_kl_decl1 :
  forall k l L P pc e t1 t2 e1' t1' l1 a2 v3,
    eval_kl (k, l) L P pc e t1 (Atom (VClos e1' t1') l1) ->
    eval_kl (k, l) L P pc e t2 a2 ->
    eval_kl (k, l) L P l1 (a2 :: e1') t1' (Atom v3 Bottom2) ->
    eval_kl (S k, l) L P pc e (TDecl t1 t2) (Atom v3 Bottom2).
Proof.
  intros. rewrite eval_kl_eq. simpl.
  replace (k - 0) with k by omega.
  exists e1'. exists t1'. exists l1. exists a2. exists v3. exists Bottom2.
  split; try split; try split; simpl; auto.
Qed.

Lemma eval_kl_decl2 :
  forall k l L P pc e t1 t2 e1' t1' l1 a2 v3,
    eval_kl (k, l) L P pc e t1 (Atom (VClos e1' t1') l1) ->
    eval_kl (k, l) L P pc e t2 a2 ->
    eval_kl (k, l) L P l1 (a2 :: e1') t1' (Atom v3 Top2) ->
    (forall a2' e2' v3',
       env_LPequiv L P (a2 :: e1') (a2' :: e2') ->
       eval_kl (l, k) L P l1 (a2' :: e2') t1' (Atom v3' Top2) ->
       value_LPequiv L P v3 v3') ->
    eval_kl (S k, l) L P pc e (TDecl t1 t2) (Atom v3 Bottom2).
Proof.
  intros. rewrite eval_kl_eq. simpl.
  replace (k - 0) with k by omega.
  exists e1'. exists t1'. exists l1. exists a2. exists v3. exists Top2.
  split; try split; try split; simpl; auto.
Qed.

Lemma eval_kl_decl_inv :
  forall k l L P pc e t1 t2 a,
    eval_kl (k, l) L P pc e (TDecl t1 t2) a ->
    (exists k' e1' t1' l1 a2 v3,
       k = S k' /\
       eval_kl (k', l) L P pc e t1 (Atom (VClos e1' t1') l1) /\
       eval_kl (k', l) L P pc e t2 a2 /\
       eval_kl (k', l) L P l1 (a2 :: e1') t1' (Atom v3 Bottom2) /\
       a = Atom v3 Bottom2) \/
    (exists k' e1' t1' l1 a2 v3,
       k = S k' /\
       eval_kl (k', l) L P pc e t1 (Atom (VClos e1' t1') l1) /\
       eval_kl (k', l) L P pc e t2 a2 /\
       eval_kl (k', l) L P l1 (a2 :: e1') t1' (Atom v3 Top2) /\
       (forall a2' e2' v3',
          env_LPequiv L P (a2 :: e1') (a2' :: e2') ->
          eval_kl (l, k') L P l1 (a2' :: e2') t1' (Atom v3' Top2) ->
          value_LPequiv L P v3 v3') /\
       a = Atom v3 Bottom2).
Proof.
  intros.
  rewrite eval_kl_eq in H.
  destruct k; simpl in H.
  - inversion H.
  - destruct H as [e1' [t1' [l1 [a2 [v3 [l3 [H1 [H2 [H3 H4]]]]]]]]].
    replace (k - 0) with k in * by omega.
    destruct l3; simpl in H4.
    + left.
      exists k. exists e1'. exists t1'. exists l1. exists a2. exists v3. auto.
    + right.
      exists k. exists e1'. exists t1'. exists l1. exists a2. exists v3. auto.
Qed.

Require Import Coq.Program.Wf.
Require Import LibTactics.
Require Export LambdaTwoSyntax IndistinguishabilityTwo.

Definition pair_lt (a b : nat * nat) : Prop :=
  fst a + snd a < fst b + snd b.

Definition bottomp : forall l : two, {l = Bottom2} + {l = Top2} :=
  fun (l : two) =>
    match l with
      | Bottom2 => left eq_refl
      | Top2 => right eq_refl
    end.

Example bottomp_example :
  (if bottomp Bottom2 then 1 else 2) = 1 /\
  (if bottomp Top2 then 1 else 2) = 2.
Proof. split; reflexivity. Qed.

Program Fixpoint eval_kl (kl : nat * nat) (L : two) (P : value -> value -> Prop)
        (pc : two) (e : env) (t : term) (a : atom) {wf pair_lt kl} : Prop :=
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
           exists e1' t1' l1 a2 a3,
             eval L P pc e t1 (Atom (VClos e1' t1') l1) _ /\
             eval L P pc e t2 a2 _ /\
             eval L P l1 (a2 :: e1') t1' a3 _ /\
             a = a3
    | TDecl t1 t2 =>
      if Compare_dec.zerop (fst kl) then False
      else let eval := eval_kl (fst kl - 1, snd kl) in
           exists e1' t1' l1 a2 v3 l3,
             eval L P pc e t1 (Atom (VClos e1' t1') l1) _ /\
             eval L P pc e t2 a2 _ /\
             eval L P l1 (a2 :: e1') t1' (Atom v3 l3) _ /\
             if bottomp l3 then a = Atom v3 Bottom2
             else let eval := eval_kl (snd kl, fst kl - 1) in
                  (forall a2' e2' v3',
                     env_LPequiv L P (a2 :: e1') (a2' :: e2') ->
                     eval L P l1 (a2' :: e2') t1' (Atom v3' Top2) _ ->
                     value_LPequiv L P v3 v3') /\
                  a = Atom v3 Bottom2
  end.

Obligation 1. unfold pair_lt. simpl in *. omega. Qed.
Obligation 2. unfold pair_lt. simpl in *. omega. Qed.
Obligation 3. unfold pair_lt. simpl in *. omega. Qed.
Obligation 4. unfold pair_lt. simpl in *. omega. Qed.
Obligation 5. unfold pair_lt. simpl in *. omega. Qed.
Obligation 6. unfold pair_lt. simpl in *. omega. Qed.
Obligation 7. unfold pair_lt. simpl in *. omega. Qed.

Definition eval_kl_type : Type :=
  {_ : nat * nat & {_ : two & {_ : value -> value -> Prop &
  {_ : two & {_ : env & {_ : term & atom}}}}}}.

Lemma eval_kl_wf' :
  forall s a,
    fst (projT1 a) + snd (projT1 a) <= s ->
    Acc (fun x y : eval_kl_type => pair_lt (projT1 x) (projT1 y)) a.
Proof.
  induction s; intros a H1.
  - destruct a as [a1 a2]; destruct a1; destruct a2; inversion H1.
    apply Acc_intro. intros y H2. inversion H2.
    + rewrite H0 in H3. inversion H3.
    + rewrite H0 in H. inversion H.
  - inversion H1 as [H2 | n H2 Heq]; auto.
    apply Acc_intro. intros y H3. inversion H3; apply IHs; omega.
Defined.

Theorem eval_kl_wf :
  well_founded (fun x y : eval_kl_type => pair_lt (projT1 x) (projT1 y)).
Proof.
  unfold well_founded; intro; eapply eval_kl_wf'; eauto.
Defined.

Obligation 8. unfold well_founded. intro. eapply eval_kl_wf'. eauto. Defined.

Definition eval (L : two) (P : value -> value -> Prop)
           (pc : two) (e : env) (t : term) (a : atom) : Prop :=
  exists k, forall l, eval_kl (k, l) L P pc e t a.

Lemma eval_kl_bool :
  forall k l L P pc e b,
    eval_kl (k, l) L P pc e (TBool b) (Atom (VBool b) pc).
Proof.
  introv. destruct k. destruct l. reflexivity. reflexivity. reflexivity.
Qed.

Lemma eval_kl_bool_inv :
  forall k l L P pc e b a,
    eval_kl (k, l) L P pc e (TBool b) a ->
    a = Atom (VBool b) pc.
Proof.
  introv Heval.
  destruct a as [v1 l1]; destruct v1 as [b1 | n1 | e1 t1];
  destruct k; destruct l; inversion Heval; reflexivity.
Qed.

Lemma eval_kl_nat :
  forall k l L P pc e n,
    eval_kl (k, l) L P pc e (TNat n) (Atom (VNat n) pc).
Proof.
  introv. destruct k. destruct l. reflexivity. reflexivity. reflexivity.
Qed.

Lemma eval_kl_nat_inv :
  forall k l L P pc e n a,
    eval_kl (k, l) L P pc e (TNat n) a ->
    a = Atom (VNat n) pc.
Proof.
  introv Heval.
  destruct a as [v1 l1]; destruct v1 as [b1 | n1 | e1 t1];
  destruct k; destruct l; inversion Heval; reflexivity.
Qed.

Lemma eval_kl_var :
  forall k l L P pc e n v' l',
    atIndex e n = Some (Atom v' l') ->
    eval_kl (k, l) L P pc e (TVar n) (Atom v' (l' ⊔ pc)).
Proof.
  introv He. destruct k. destruct l.
  exists v' l'. auto. exists v' l'. auto. exists v' l'. auto.
Qed.

Lemma eval_kl_var_inv :
  forall k l L P pc e n a,
    eval_kl (k, l) L P pc e (TVar n) a ->
    exists v' l',
      atIndex e n = Some (Atom v' l') /\
      a = Atom v' (l' ⊔ pc).
Proof.
  introv Heval.
  destruct a as [v1 l1]; destruct v1 as [b1 | n1 | e1 t1];
  destruct k; destruct l; inversion Heval; auto.
Qed.

Lemma eval_kl_abs :
  forall k l L P pc e t',
    eval_kl (k, l) L P pc e (TAbs t') (Atom (VClos e t') pc).
Proof.
  introv. destruct k. destruct l. reflexivity. reflexivity. reflexivity.
Qed.
  
Lemma eval_kl_abs_inv :
  forall k l L P pc e t' a,
    eval_kl (k, l) L P pc e (TAbs t') a ->
    a = Atom (VClos e t') pc.
Proof.
  introv Heval.
  destruct a as [v1 l1]; destruct v1 as [b1 | n1 | e1 t1];
  destruct k; destruct l; inversion Heval; reflexivity.
Qed.

Lemma eval_kl_app :
  forall k l L P pc e t1 t2 e1' t1' l1 a2 a3,
    eval_kl (k, l) L P pc e t1 (Atom (VClos e1' t1') l1) ->
    eval_kl (k, l) L P pc e t2 a2 ->
    eval_kl (k, l) L P l1 (a2 :: e1') t1' a3 ->
    eval_kl (S k, l) L P pc e (TApp t1 t2) a3.
Proof.
  (* TODO *)
  Admitted.

Lemma eval_kl_app_inv :
  forall k l L P pc e t1 t2 a,
    eval_kl (k, l) L P pc e (TApp t1 t2) a ->
    exists k' e1' t1' l1 a2 a3,
      k = S k' /\
      eval_kl (k', l) L P pc e t1 (Atom (VClos e1' t1') l1) /\
      eval_kl (k', l) L P pc e t2 a2 /\
      eval_kl (k', l) L P l1 (a2 :: e1') t1' a3 /\
      a = a3.
Proof.
  (* TODO *)
  Admitted.

Lemma eval_kl_decl1 :
  forall k l L P pc e t1 t2 e1' t1' l1 a2 v3,
    eval_kl (k, l) L P pc e t1 (Atom (VClos e1' t1') l1) ->
    eval_kl (k, l) L P pc e t2 a2 ->
    eval_kl (k, l) L P l1 (a2 :: e1') t1' (Atom v3 Bottom2) ->
    eval_kl (S k, l) L P pc e (TDecl t1 t2) (Atom v3 Bottom2).
Proof.
  (* TODO *)
  Admitted.

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
  (* TODO *)
  Admitted.

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
  (* TODO *)
  Admitted.

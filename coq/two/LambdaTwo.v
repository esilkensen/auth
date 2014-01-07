Require Import Recdef Wf_nat.
Require Import LibTactics.
Require Export LambdaTwoSyntax IndistinguishabilityTwo.

Definition pair_lt (a b : nat * nat) : Prop :=
  fst a + snd a < fst b + snd b.

Lemma pair_lt_wf' :
  forall s a, fst a + snd a <= s -> Acc pair_lt a.
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
                  else let eval := eval_kl (fst kl - 1, snd kl) _ in
                       exists e1' t1' l1 a2 a3,
                         eval L P pc e t1 (Atom (VClos e1' t1') l1) /\
                         eval L P pc e t2 a2 /\
                         eval L P l1 (a2 :: e1') t1' a3 /\
                         a = a3
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

Definition eval (L : two) (P : value -> value -> Prop)
           (pc : two) (e : env) (t : term) (a : atom) : Prop :=
  exists k, forall l, eval_kl (k, l) L P pc e t a.

Lemma eval_kl_bool :
  forall k l L P pc e b,
    eval_kl (k, l) L P pc e (TBool b) (Atom (VBool b) pc).
Proof.
  introv. destruct k; destruct l; reflexivity.
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
  introv. destruct k; destruct l; reflexivity.
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
  introv He. destruct k; destruct l; exists v' l'; auto.
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
  introv. destruct k; destruct l; reflexivity.
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

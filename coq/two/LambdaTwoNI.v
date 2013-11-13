Require Import Program.Tactics.
Require Import LambdaTwo.
Require Import LibTactics.

Section NI.

Lemma non_interference_bool :
  forall (k : nat) (L : two) (P : value -> value -> Prop)
         (pc : two) (e1 e2 : env) (b : bool) (a1 a2 : atom),
    (forall v, P v v) ->
    env_LPequiv L P e1 e2 ->
    eval_k k L P pc e1 (TBool b) a1 ->
    eval_k k L P pc e2 (TBool b) a2 ->
    atom_LPequiv L P a1 a2.
Proof.
  introv Prefl He Heval1 Heval2.
  destruct k;
    (destruct L; destruct pc;
     simpl in Heval1; simpl in Heval2; subst; [
       right; left; auto |
       left; auto |
       right; right; auto |
       right; right; auto
     ]).
Qed.

Hint Resolve non_interference_bool.

Lemma non_interference_nat :
  forall (k : nat) (L : two) (P : value -> value -> Prop)
         (pc : two) (e1 e2 : env) (n : nat) (a1 a2 : atom),
    (forall v, P v v) ->
    env_LPequiv L P e1 e2 ->
    eval_k k L P pc e1 (TNat n) a1 ->
    eval_k k L P pc e2 (TNat n) a2 ->
    atom_LPequiv L P a1 a2.
Proof.
  introv Prefl He Heval1 Heval2.
  destruct k;
    (destruct L; destruct pc;
     simpl in Heval1; simpl in Heval2; subst; [
       right; left; auto |
       left; auto |
       right; right; auto |
       right; right; auto
     ]).
Qed.

Hint Resolve non_interference_nat.

Lemma non_interference_var :
  forall (k : nat) (L : two) (P : value -> value -> Prop)
         (pc : two) (e1 e2 : env) (n : nat) (a1 a2 : atom),
    (forall v, P v v) ->
    env_LPequiv L P e1 e2 ->
    eval_k k L P pc e1 (TVar n) a1 ->
    eval_k k L P pc e2 (TVar n) a2 ->
    atom_LPequiv L P a1 a2.
Proof.
  introv Prefl He Heval1 Heval2.
  destruct k;
    simpl in Heval1; simpl in Heval2;
    destruct Heval1 as [v1 [l1 Ha1]];
    destruct Heval2 as [v2 [l2 Ha2]];
    destruct_conjs; subst;
    assert (Ha: atom_LPequiv L P (Atom v1 l1) (Atom v2 l2)) by
        (eapply list_forall2_atIndex; eauto);
    assert (l2 = l1) by
        (apply atom_LPequiv_lab_inv in Ha; auto);
    destruct pc; destruct l1; subst; auto;
    apply atom_LPequiv_raise; assumption.
Qed.

Hint Resolve non_interference_var.

Lemma non_interference_abs :
  forall (k : nat) (L : two) (P : value -> value -> Prop)
         (pc : two) (e1 e2 : env) (t : term) (a1 a2 : atom),
    (forall v, P v v) ->
    env_LPequiv L P e1 e2 ->
    eval_k k L P pc e1 (TAbs t) a1 ->
    eval_k k L P pc e2 (TAbs t) a2 ->
    atom_LPequiv L P a1 a2.
Proof.
  introv Prefl He Heval1 Heval2.
  destruct k;
    (simpl in Heval1; simpl in Heval2;
     destruct L; destruct pc; subst; [
       right; left; auto |
       left; auto |
       right; right; auto |
       right; right; auto
     ]).
Qed.

Hint Resolve non_interference_abs.
  
Theorem non_interference_strong_observer :
  forall (k : nat) (L : two) (P : value -> value -> Prop)
         (pc : two) (e1 e2 : env) (t : term) (a1 a2 : atom),
    (forall v, P v v) ->
    env_LPequiv L P e1 e2 ->
    eval_k k L P pc e1 t a1 -> 
    eval_k k L P pc e2 t a2 -> 
    atom_LPequiv L P a1 a2.
Proof.
  introv Prefl He Heval1 Heval2;
  gen pc e1 e2 t a1 a2.
  induction k as [| k']; intros; destruct t; eauto.
  - (* E_App *)
    rename a1 into a; rename a2 into a';
    rename e1 into e; rename e2 into e'.
    simpl in Heval1; simpl in Heval2.
    destruct Heval1 as
        [e1' [t1' [l1 [a2 [a3 [Heval1_1 [Heval1_2 [Heval1_3 Ha]]]]]]]];
      destruct Heval2 as
        [e2' [t2' [l2 [a2' [a3' [Heval2_1 [Heval2_2 [Heval2_3 Ha']]]]]]]].
    remember (Atom (VClos e1' t1') l1) as a1.
    remember (Atom (VClos e2' t2') l2) as a1'.
    assert (IH1: atom_LPequiv L P a1 a1') by (eapply IHk'; eauto).
    assert (l2 = l1) by
        (subst; apply atom_LPequiv_lab_inv in IH1; auto); subst.
    assert (Hte': t2' = t1' /\ env_LPequiv L P e1' e2') by
        (split; destruct IH1; destruct H; destruct_conjs; auto);
      destruct Hte' as [Ht He']; subst.
    assert (IH2: atom_LPequiv L P a2 a2') by (apply (IHk' pc e e' He t2); auto).
    assert (Hae': env_LPequiv L P (a2 :: e1') (a2' :: e2')) by (split; auto).
    eapply IHk'; eauto.
  - (* E_Decl *)
    rename a1 into a; rename a2 into a';
    rename e1 into e; rename e2 into e'.
    simpl in Heval1; simpl in Heval2.
    destruct Heval1 as
        [e1' [t1' [l1 [a2 [v3 [l3 [Heval1_1 [Heval1_2 [Heval1_3 HP1]]]]]]]]];
      destruct Heval2 as
        [e2' [t2' [l2 [a2' [v3' [l3' [Heval2_1 [Heval2_2 [Heval2_3 HP2]]]]]]]]].
    remember (Atom (VClos e1' t1') l1) as a1.
    remember (Atom (VClos e2' t2') l2) as a1'.
    assert (IH1: atom_LPequiv L P a1 a1') by (eapply IHk'; eauto).
    assert (l2 = l1) by
        (subst; apply atom_LPequiv_lab_inv in IH1; auto); subst.
    assert (Hte': t2' = t1' /\ env_LPequiv L P e1' e2') by
        (split; subst; destruct IH1; destruct H; destruct_conjs; auto);
      destruct Hte' as [Ht' He']; subst.
    assert (IH2: atom_LPequiv L P a2 a2') by (apply (IHk' pc e e' He t2); auto).
    assert (Hae': env_LPequiv L P (a2 :: e1') (a2' :: e2')) by (split; auto).
    assert (IH3: atom_LPequiv L P (Atom v3 l3) (Atom v3' l3')) by
        (eapply IHk'; eauto).
    assert (l3' = l3) by (apply atom_LPequiv_lab_inv in IH3; auto); subst.
    destruct l3; subst; auto.
    destruct HP1 as [HP1 Ha1]; destruct HP2 as [HP2 Ha2]; subst.
    assert (value_LPequiv L P v3 v3') by (eapply HP1; eauto).
    destruct L; right.
    + left. auto.
    + right. auto.
Qed.

Theorem non_interference :
  forall k L P pc e1 e2 t a1 a2,
    env_LPequiv L P e1 e2 ->
    eval_k k L P pc e1 t a1 ->
    eval_k k L P pc e2 t a2 ->
    (forall x, P x x) ->
    atom_Lequiv L a1 a2.
Proof.
  introv He Heval1 Heval2 Prefl.
  eapply non_interference_strong_observer in Heval2; eauto.
  eapply atom_LPequiv_Lequiv. eassumption.
Qed.
  
End NI.

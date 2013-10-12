Require Import MyTactics.
Require Import LabelAlgebra.
Require Import Lambda.
Require Import TermEquiv.
Require Import Auth.
Require Import BooleanIndistinguishability.
Require Import Indistinguishability.
Require Import IndistinguishabilityComparison.

Set Implicit Arguments.

Section NI.

Context {A L: Type} {LA: LabelAlgebra A L} (auth: A) (lab: L).

(** * Preliminary lemmas. *)
(** ** The pc label is below the label of the resulting atom. *)
Lemma eval_pc_lower_bound :
  forall pc e t v l,
    env_auth e ≤ auth ->
    term_auth t ≤ auth ->
    pc; e ⊢ t ⇓ Atom v l ->
    pc ⊑[auth] l.
Proof.
intros pc e t v l Hauthe Hautht Heval.
remember (Atom v l) as a.
generalize dependent l. generalize dependent v.
induction Heval; intros v' l' Heq; inversion Heq; subst; simpl in *; auto.
* transitivity l1. eauto.
  apply @eval_auth_upper_bound with (auth := auth) in Heval1; auto.
  unfold atom_auth in Heval1. fold atom_auth in Heval1. fold (env_auth e1') in Heval1.
  apply IHHeval3 with (v := v'); auto.
  + apply @eval_auth_upper_bound with (auth := auth) in Heval2; eauto.
  + eauto.
  + eauto.
* transitivity l1; eauto.
Qed.

(** ** Strong version of the non-interference theorem. *)
Lemma NI_strong :
  forall pc1 pc2 e1 e2 t1 t2 a1 a2,
    env_auth e1 ≤ auth ->
    term_auth t1 ≤ auth ->
    env_auth e2 ≤ auth ->
    term_auth t2 ≤ auth ->
    pc1 =L pc2 ->
    env_Lequiv auth lab e1 e2 ->
    term_equiv t1 t2 ->
    pc1; e1 ⊢ t1 ⇓ a1 ->
    pc2; e2 ⊢ t2 ⇓ a2 ->
    atom_Lequiv auth lab a1 a2.
Proof.
intros pc pc' e e' t t' a a' Hauthe Hautht Hauthe' Hautht' Hpc He Ht Heval.
generalize dependent a'.
generalize dependent t'.
generalize dependent e'.
generalize dependent pc'.
induction Heval; intros pc' Hpc e' Hauthe' He t' Hautht' Ht a' Heval';
destruct t'; simpl in Ht; simpl in Hautht; simpl in Hautht';
try tauto; inversion Heval'; subst.
* rename b0 into b. intro Hlab. auto.
* rename n0 into n. intro Hlab. auto.
* rename n0 into n. rename v0 into v'. rename l0 into l'.
  intro Hlab. fold (value_Lequiv auth lab v v').
  assert (l ⊑[auth] lab \/ l' ⊑[auth] lab) as Hlab'.
  { destruct Hlab; [left | right].
    transitivity (l ⊔ pc); auto.
    transitivity (l' ⊔ pc'); auto.
  }
  pose proof (list_forall2_atIndex _ _ _ _ _ _ He H H3) as Hatom.
  specialize (Hatom Hlab'). fold (value_Lequiv auth lab v v') in Hatom.
  destruct Hatom as [Hv Hl]. split; auto.
  rewrite Hl. rewrite Hpc. reflexivity.
* intro Hlab. fold (atom_Lequiv auth lab). fold (env_Lequiv auth lab e e').
  splits; auto.
* rename l0 into l1'. rename a0 into a2'.
  destruct Ht as [Ht1 Ht2].
  assert (term_auth t1 ≤ auth) as Hautht1 by eauto.
  assert (term_auth t2 ≤ auth) as Hautht2 by eauto.
  clear Hautht.
  assert (term_auth t'1 ≤ auth) as Hautht'1 by eauto.
  assert (term_auth t'2 ≤ auth) as Hautht'2 by eauto.
  clear Hautht'.
  specialize (IHHeval1 Hauthe Hautht1 _ Hpc _ Hauthe' He _ Hautht'1 Ht1 _ H1).
  specialize (IHHeval2 Hauthe Hautht2 _ Hpc _ Hauthe' He _ Hautht'2 Ht2 _ H4).
  destruct a3 as [v3  l3].
  destruct a' as [v'3 l'3].
  intro Hlab. fold (value_Lequiv auth lab v3 v'3).
  assert (l1 ⊑[auth] lab \/ l1' ⊑[auth] lab) as Hlab1.
  { destruct Hlab; [left | right].
    + transitivity l3; auto.
      apply @eval_auth_upper_bound with (auth := auth) in Heval1; auto.
      simpl in Heval1.
      apply @eval_auth_upper_bound with (auth := auth) in Heval2; auto.
      apply eval_pc_lower_bound in Heval3; simpl; eauto.
    + transitivity l'3; auto.
      apply @eval_auth_upper_bound with (auth := auth) in H1; auto.
      simpl in H1.
      apply @eval_auth_upper_bound with (auth := auth) in H4; auto.
      apply eval_pc_lower_bound in H6; simpl; eauto.
  }
  specialize (IHHeval1 Hlab1).
  destruct IHHeval1 as [[He1' Ht1'] Hl1].
  fold (atom_Lequiv auth lab) in He1'.
  fold (env_Lequiv auth lab e1' e1'0) in He1'.
  assert (env_auth e1' ∨ atom_auth a2 ≤ auth) as Hautha2e1'.
  { apply join_lub.
    + apply @eval_auth_upper_bound with (auth := auth) in Heval1; auto.
      simpl in Heval1. eauto.
    + apply @eval_auth_upper_bound with (auth := auth) in Heval2; auto.
  }
  assert (term_auth t1' ≤ auth) as Hautht1'.
  { apply @eval_auth_upper_bound with (auth := auth) in Heval1; auto.
    simpl in Heval1. eauto.
  }
  assert (env_auth e1'0 ∨ atom_auth a2' ≤ auth) as Hautha2'e1'0.
  { apply join_lub.
    + apply @eval_auth_upper_bound with (auth := auth) in H1; auto.
      simpl in H1. eauto.
    + apply @eval_auth_upper_bound with (auth := auth) in H4; auto.
  }
  assert (term_auth t1'0 ≤ auth) as Hautht1'0.
  { apply @eval_auth_upper_bound with (auth := auth) in H1; auto.
    simpl in H1. eauto.
  }
  specialize
  (IHHeval3 Hautha2e1' Hautht1'
            _ Hl1
            (a2' :: e1'0) Hautha2'e1'0 (conj IHHeval2 He1')
            _ Hautht1'0 Ht1' _ H6).
  specialize (IHHeval3 Hlab).
  fold (value_Lequiv auth lab v3 v'3) in IHHeval3.
  assumption.
* rename a0 into a'. rename l0 into l'. rename v0 into v1'. rename l3 into l1'.
  destruct Ht as [Ht [Ha Hl]].
  rename Hautht into Hauthta.
  assert (term_auth t ≤ auth) as Hautht by eauto.
  assert (a ≤ auth) as Hautha by eauto.
  clear Hauthta.
  rename Hautht' into Hautht'a'.
  assert (term_auth t' ≤ auth) as Hautht' by eauto.
  assert (a' ≤ auth) as Hautha' by eauto.
  clear Hautht'a'.
  specialize (IHHeval Hauthe Hautht _ Hpc _ Hauthe' He _ Hautht' Ht _ H6).
  intro Hlab. fold (value_Lequiv auth lab v1 v1').
  assert (l1 ⊑[auth]lab \/ l1' ⊑[auth]lab) as Hlab'.
  { destruct Hlab; [left | right].
    + transitivity l;  eauto.
    + transitivity l'; eauto.
  }
  specialize (IHHeval Hlab'). fold (value_Lequiv auth lab v1 v1') in IHHeval.
  destruct IHHeval. split; auto.
Qed.

(** * General non-interference theorem. *)
Theorem general_non_interference :
  forall pc e1 e2 t a1 a2,
    env_auth e1 ≤ auth ->
    env_auth e2 ≤ auth ->
    term_auth t ≤ auth ->
    env_Lequiv auth lab e1 e2 ->
    pc; e1 ⊢ t ⇓ a1 ->
    pc; e2 ⊢ t ⇓ a2 ->
    atom_Lequiv auth lab a1 a2.
Proof.
intros pc e1 e2 t a1 a2 Hauthe1 Hauthe2 Hautht Henv Heval1 Heval2.
apply NI_strong
with (pc1 := pc) (pc2 := pc) (e1 := e1) (e2 := e2) (t1 := t) (t2 := t); auto.
Qed.

(** * Boolean non-interference theorem. *)
Theorem boolean_non_interference :
  forall pc e1 e2 t b1 b2 l1 l2,
    term_auth t ≤ auth ->
    bool_env_Lequiv auth lab e1 e2 ->
    pc; e1 ⊢ t ⇓ Atom (VBool b1) l1 ->
    pc; e2 ⊢ t ⇓ Atom (VBool b2) l2 ->
    atom_Lequiv auth lab (Atom (VBool b1) l1) (Atom (VBool b2) l2).
Proof.
intros pc e1 e2 t b1 b2 l1 l2 Hautht Henv Heval1 Heval2.
apply general_non_interference
with (pc := pc) (e1 := e1) (e2 := e2) (t := t); auto.
* apply env_bool_Lequiv_auth_bottom_left in Henv. rewrite Henv. auto.
* apply env_bool_Lequiv_auth_bottom_right in Henv. rewrite Henv. auto.
* auto using bool_env_Lequiv_env_Lequiv.
Qed.


End NI.

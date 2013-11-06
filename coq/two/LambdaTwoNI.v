Require Import Program.Tactics.
Require Import LambdaTwo.
Require Import LibTactics.

Section NI.

Theorem non_interference_strong_observer :
  forall L P k pc e1 e2 t a1 a2,
    env_LPequiv L P e1 e2 ->
    eval L P pc e1 t k a1 -> 
    eval L P pc e2 t k a2 -> 
    (forall x, P x x) ->
    atom_LPequiv L P a1 a2.
Proof.
  introv He Heval1 Heval2 Prefl.
  gen pc e1 e2 t a1 a2.
  induction k as [| k']; intros; destruct t; auto.
  - (* E_Nat *)
    simpl in Heval1; simpl in Heval2; subst.
    destruct L; destruct pc.
    + right. left. auto.
    + left. auto.
    + right. right. auto.
    + right. right. auto.
  - (* E_Var *)
    simpl in Heval1; simpl in Heval2; subst.
    destruct Heval1 as [v1 [l1 [H1 H2]]].
    destruct Heval2 as [v2 [l2 [H1' H2']]].
    assert (Ha: atom_LPequiv L P (Atom v1 l1) (Atom v2 l2)) by
        (eapply list_forall2_atIndex; eauto).
    assert (l2 = l1) by
        (apply atom_LPequiv_lab_inv in Ha; auto).
    destruct pc; destruct l1; subst; auto;
    apply atom_LPequiv_raise; assumption.
  - (* E_Abs *)
    simpl in Heval1; simpl in Heval2; subst.
    destruct L; destruct pc.
    + right. left. auto.
    + left. auto.
    + right. right. auto.
    + right. right. auto.
  - (* E_App *)
    rename a1 into a; rename a2 into a'.
    rename e1 into e; rename e2 into e'.
    simpl in Heval1; simpl in Heval2.
    destruct Heval1 as
        [e1' [t1' [l1 [a2 [a3 [H1 [H2 [H3 Ha]]]]]]]].
    destruct Heval2 as
        [e2' [t2' [l2 [a2' [a3' [H1' [H2' [H3' Ha']]]]]]]].
    remember (Atom (VClos e1' t1') l1) as a1.
    remember (Atom (VClos e2' t2') l2) as a1'.
    assert (IH1: atom_LPequiv L P a1 a1') by
        (eapply IHk'; eauto).
    assert (l2 = l1) by
        (subst; apply atom_LPequiv_lab_inv in IH1; auto).
    assert (t2' = t1' /\ env_LPequiv L P e1' e2') by
        (split; subst; destruct IH1 as [H |];
         destruct H; destruct_conjs; auto).
    destruct_conjs; subst.
    assert (IH2: atom_LPequiv L P a2 a2') by
        (apply (IHk' pc e e' He t2); auto).
    assert (env_LPequiv L P (a2 :: e1') (a2' :: e2')) by
        (split; auto).
    eapply IHk'; eauto.
  - (* E_Decl *)
    rename a1 into a; rename a2 into a'.
    rename e1 into e; rename e2 into e'.
    simpl in Heval1; simpl in Heval2.
    destruct Heval1 as
        [e1' [t1' [l1 [a2 [v3 [l3 [H1 [H2 [H3 H4]]]]]]]]].
    destruct Heval2 as
        [e2' [t2' [l2 [a2' [v3' [l3' [H1' [H2' [H3' H4']]]]]]]]].
    remember (Atom (VClos e1' t1') l1) as a1.
    remember (Atom (VClos e2' t2') l2) as a1'.
    assert (IH1: atom_LPequiv L P a1 a1') by
        (eapply IHk'; eauto).
    assert (l2 = l1) by
        (subst; apply atom_LPequiv_lab_inv in IH1; auto).
    assert (t2' = t1' /\ env_LPequiv L P e1' e2') by
        (split; subst; destruct IH1 as [H |];
         destruct H; destruct_conjs; auto).
    destruct_conjs; subst.
    assert (IH2: atom_LPequiv L P a2 a2') by
        (apply (IHk' pc e e' He t2); auto).
    assert (env_LPequiv L P (a2 :: e1') (a2' :: e2')) by
        (split; auto).
    assert (IH3: atom_LPequiv L P (Atom v3 l3) (Atom v3' l3')) by
        (eapply IHk'; eauto).
    assert (l3' = l3) by
        (apply atom_LPequiv_lab_inv in IH3; auto); subst.
    destruct l3; subst; auto.
    destruct_conjs; subst.
    assert (value_LPequiv L P v3 v3') by
        (eapply H4; eauto).
    destruct L.
    + right. left. auto.
    + right. right. auto.
Qed.

Theorem non_interference :
  forall L (P : value -> value -> Prop) k pc e1 e2 t a1 a2,
    (forall x, P x x) ->
    env_LPequiv L P e1 e2 ->
    eval L P pc e1 t k a1 ->
    eval L P pc e2 t k a2 ->
    atom_Lequiv L a1 a2.
Proof.
  intros L P k pc e1 e2 t a1 a2 Prefl He Heval1 Heval2.
  eapply non_interference_strong_observer in Heval2; eauto.
  eapply atom_LPequiv_Lequiv. eassumption.
Qed.
  
End NI.

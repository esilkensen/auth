Require Import Program.Tactics.
Require Import MyTactics.
Require Import LabelAlgebra.
Require Import LambdaTwo.
Require Import TermEquivTwo.

(** * Indistinguishability relations. *) 
Section IndistinguishabilityTwo.

Context (L : two)
        (P : value -> value -> Prop)
        (Prefl : forall x, P x x)
        (Psym : forall x y, P x y -> P y x)
        (Ptrans : forall x y z, P x y -> P y z -> P x z).

Fixpoint atom_Lequiv a1 a2 : Prop :=
  match a1, a2 with
    | Atom v1 l1, Atom v2 l2 =>
      (L = Bottom2 /\ l1 = l2 /\ l1 = Top2 /\ P v1 v2) \/
      (L = Bottom2 /\ l1 = l2 /\ l1 = Bottom2 /\ value_Lequiv v1 v2) \/
      (L = Top2 /\ l1 = l2 /\ value_Lequiv v1 v2)
  end
with value_Lequiv v1 v2 : Prop :=
       match v1, v2 with
         | VNat n1, VNat n2 => n1 = n2
         | VClos e1 t1, VClos e2 t2 =>
           list_forall2 atom_Lequiv e1 e2 /\ term_equiv t1 t2
         | VNat _, _ | VClos _ _, _ => False
       end.

Definition env_Lequiv : env -> env -> Prop :=
  list_forall2 atom_Lequiv.

Lemma atom_Lequiv_lab_inv :
  forall v1 v2 l1 l2,
    atom_Lequiv (Atom v1 l1) (Atom v2 l2) ->
    l1 = l2.
Proof.
  intros. inversion H; inversion H0; destruct_conjs; auto.
Qed.

(** ** The indistinguishability relations are equivalences. *)
Lemma atom_value_env_Lequiv_refl :
  (forall a, atom_Lequiv a a)
  /\ (forall v, value_Lequiv v v)
  /\ (forall e, env_Lequiv e e).
Proof.
  apply atom_value_env_mutind; intros; simpl; auto.
  destruct L; destruct l; auto. right. auto.
  induction l.
    reflexivity.
    simpl. split.
      apply (H 0 a). reflexivity.
      apply IHl. intros n b Hb. apply (H (S n) b). assumption.
Qed.

Lemma atom_value_env_Lequiv_sym :
  (forall a1 a2, atom_Lequiv a1 a2 -> atom_Lequiv a2 a1)
  /\ (forall v1 v2, value_Lequiv v1 v2 -> value_Lequiv v2 v1)
  /\ (forall e1 e2, env_Lequiv e1 e2 -> env_Lequiv e2 e1).
Proof.
  apply atom_value_env_mutind; intros. 
  destruct a2. simpl. simpl in H0.
  destruct H0; destruct H0; destruct_conjs; destruct L; subst; inversion H0.
    left. auto.
    right. left. auto.
    right. right. auto.
  destruct v2; inversion H. reflexivity.
  destruct v2. 
    destruct l; simpl in H0; inversion H0.
    destruct l.
      destruct l0.
        inversion H0. simpl. split. reflexivity. symmetry. assumption.
        simpl in H0. inversion H0. inversion H1.
      simpl. split. apply H.
        destruct l0; inversion H0; inversion H1; auto.
        inversion H0. symmetry. assumption.
  generalize dependent e2.
  induction l; intros e2 H2; destruct e2; simpl in *; try tauto.
  split. apply (H 0). reflexivity. inversion H2. assumption.
  apply IHl. intros n b Hb. apply (H (S n) b). assumption. tauto.
Qed.

Lemma atom_value_env_Lequiv_trans :
  (forall a1 a2 a3,
     atom_Lequiv a1 a2 -> atom_Lequiv a2 a3 -> atom_Lequiv a1 a3)
  /\ (forall v1 v2 v3,
        value_Lequiv v1 v2 -> value_Lequiv v2 v3 -> value_Lequiv v1 v3)
  /\ (forall e1 e2 e3,
        env_Lequiv e1 e2 -> env_Lequiv e2 e3 -> env_Lequiv e1 e3).
Proof.
  apply atom_value_env_mutind; intros.
  destruct a2. destruct a3. simpl in *.
  destruct H0; destruct H0; destruct H1; destruct H1;
  destruct_conjs; subst; destruct L; destruct t0; try clear_dup; inversion H0;
  try inversion H1; try inversion H2; try inversion H3; try inversion H4.
    apply (Ptrans v v0 v1) in H7. left. auto. assumption.
    apply (H v0 v1) in H4. right. left. auto. assumption.
    apply (H v0 v1) in H3. right. right. auto. assumption.
    apply (H v0 v1) in H3. right. right. auto. assumption.
    destruct v2; destruct v3; simpl in *; auto.
    destruct v2; destruct v3; simpl in *; auto.
      unfold env_Lequiv in H.
      destruct H0. destruct H1. split.
        apply (H l0 l1). assumption. assumption.
        transitivity t0; assumption.
    generalize dependent e3. generalize dependent e2.
    induction l; intros e2 H12 e3 H23; destruct e2; simpl in *;
    destruct e3; try tauto. destruct H12. destruct H23.
    split.
      apply H with (n:=0) (a2:=a0); tauto.
      apply IHl with (e2:=e2); try tauto.
        intros n b Hb. apply (H (S n) b). assumption.
Qed.
    
Global Instance Equivalence_atom_Lequiv : Equivalence atom_Lequiv.
Proof.
constructor.
* destruct atom_value_env_Lequiv_refl as [? _]. assumption.
* destruct atom_value_env_Lequiv_sym as [? _]. assumption.
* destruct atom_value_env_Lequiv_trans as [? _]. assumption.
Qed.

Global Instance Equivalence_value_Lequiv : Equivalence value_Lequiv.
Proof.
constructor.
* destruct atom_value_env_Lequiv_refl as [_ [? _]]. assumption.
* destruct atom_value_env_Lequiv_sym as [_ [? _]]. assumption.
* destruct atom_value_env_Lequiv_trans as [_ [? _]]. assumption.
Qed.

Global Instance Equivalence_env_Lequiv : Equivalence env_Lequiv.
Proof.
constructor.
* destruct atom_value_env_Lequiv_refl as [_ [_ ?]]. assumption.
* destruct atom_value_env_Lequiv_sym as [_ [_ ?]]. assumption.
* destruct atom_value_env_Lequiv_trans as [_ [_ ?]]. assumption.
Qed.

End IndistinguishabilityTwo.

Require Import MyTactics.
Require Import LabelAlgebra.
Require Import Lambda.

Set Implicit Arguments.

(** * Authority of terms, atoms, values, environments. **)
Section Auth.

Context {A L: Type} {LA: LabelAlgebra A L}.

Fixpoint term_auth (t: term A L) : A :=
match t with
| TBool _ | TNat _ | TVar _ => bottom
| TLam t => term_auth t
| TApp t1 t2 => term_auth t1 ∨ term_auth t2
| TRelabel t auth _ => term_auth t ∨ auth
end.

Fixpoint atom_auth (a: atom A L) : A :=
match a with
| Atom v _ => value_auth v
end
with value_auth (v: value A L) : A :=
match v with
| VBool _ | VNat _ => bottom
| VClos e t =>
  fold_right (fun a auth => auth ∨ atom_auth a) bottom e
  ∨ term_auth t
end.

Definition env_auth (e: env A L) : A :=
  fold_right (fun a auth => auth ∨ atom_auth a) bottom e.

Lemma env_auth_upper_bound (auth: A) (e: env A L) :
  forall n a,
    env_auth e ≤ auth ->
    atIndex e n = Some a ->
    atom_auth a ≤ auth.
Proof.
induction e; intros n b He Hn; simpl in *; auto.
destruct n; simpl in Hn.
* inversion Hn. subst b. eauto.
* eauto.
Qed.

(** If the authority of the inputs and the program are bounded, then the authority of the result is also below that bound. *)
Lemma eval_auth_upper_bound :
  forall auth pc e t a,
    env_auth e ≤ auth ->
    term_auth t ≤ auth ->
    pc; e ⊢ t ⇓ a ->
    atom_auth a ≤ auth.
Proof.
intros auth pc e t a He Ht Heval. induction Heval; simpl in *; auto.
* transitivity (atom_auth (Atom v l)); auto.
  eauto using env_auth_upper_bound.
* apply IHHeval3.
  - apply join_lub; eauto.
  - eauto.
* eauto.
Qed.

End Auth.

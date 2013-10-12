Require Import RelationClasses.

(** * Iterated splits. *)
(** Version that does not unfold definitions. *)
(** This version of splits is careful to using large conjunctions in order to reduce typechecking time. *)
Inductive and4 (A B C D: Prop) : Prop :=
| conj4: A -> B -> C -> D -> and4 A B C D.
Hint Constructors and4.

Lemma and4_1 (A B C D: Prop) :
  and4 A B C D -> A /\ B /\ C /\ D.
Proof.
intros [HA HB HC HD]. tauto.
Qed.

Lemma and4_2 (A B C D: Prop) :
  and4 A B C D -> (A /\ B) /\ C /\ D.
Proof.
intros [HA HB HC HD]. tauto.
Qed.

Lemma and4_3 (A B C D: Prop) :
  and4 A B C D -> (A /\ B /\ C) /\ D.
Proof.
intros [HA HB HC HD]. tauto.
Qed.

Lemma and4_4 (A B C D: Prop) :
  and4 A B C D -> ((A /\ B) /\ C) /\ D.
Proof.
intros [HA HB HC HD]. tauto.
Qed.

Inductive and8 (A B C D E F G H: Prop) : Prop :=
| conj8: A -> B -> C -> D -> E -> F -> G -> H -> and8 A B C D E F G H.
Hint Constructors and8.

Lemma and8_intro (A B C D E F G H: Prop) :
  and8 A B C D E F G H -> A /\ B /\ C /\ D /\ E /\ F /\ G /\ H.
Proof.
intros [HA HB HC HD HE HF HG HH]. tauto.
Qed.

Inductive and16 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16: Prop) : Prop :=
| conj16:
    A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 ->
    A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 ->
    and16 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16.
Hint Constructors and16.

Lemma and16_intro (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16: Prop) :
  and16 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 ->
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\
  A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16.
Proof.
intro H. decompose record H. tauto.
Qed.

Inductive and32 (A1 A2 A3 A4 A5 A6 A7 A8
                 A9 A10 A11 A12 A13 A14 A15 A16
                 A17 A18 A19 A20 A21 A22 A23 A24
                 A25 A26 A27 A28 A29 A30 A31 A32: Prop) : Prop :=
| conj32:
    A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 ->
    A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 ->
    A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 ->
    A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 ->
    and32 A1 A2 A3 A4 A5 A6 A7 A8
          A9 A10 A11 A12 A13 A14 A15 A16
          A17 A18 A19 A20 A21 A22 A23 A24
          A25 A26 A27 A28 A29 A30 A31 A32.
Hint Constructors and32.

Lemma and32_intro (A1 A2 A3 A4 A5 A6 A7 A8
               A9 A10 A11 A12 A13 A14 A15 A16
               A17 A18 A19 A20 A21 A22 A23 A24
               A25 A26 A27 A28 A29 A30 A31 A32: Prop) :
  and32 A1 A2 A3 A4 A5 A6 A7 A8
        A9 A10 A11 A12 A13 A14 A15 A16
        A17 A18 A19 A20 A21 A22 A23 A24
        A25 A26 A27 A28 A29 A30 A31 A32 ->
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\
  A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\
  A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\
  A25 /\ A26 /\ A27 /\ A28 /\ A29 /\ A30 /\ A31 /\ A32.
Proof.
intro H. decompose record H. tauto.
Qed.

Inductive and64 (A1 A2 A3 A4 A5 A6 A7 A8
                 A9 A10 A11 A12 A13 A14 A15 A16
                 A17 A18 A19 A20 A21 A22 A23 A24
                 A25 A26 A27 A28 A29 A30 A31 A32
                 A33 A34 A35 A36 A37 A38 A39 A40
                 A41 A42 A43 A44 A45 A46 A47 A48
                 A49 A50 A51 A52 A53 A54 A55 A56
                 A57 A58 A59 A60 A61 A62 A63 A64: Prop) : Prop :=
| conj64:
    A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 ->
    A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 ->
    A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 ->
    A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 ->
    A33 -> A34 -> A35 -> A36 -> A37 -> A38 -> A39 -> A40 ->
    A41 -> A42 -> A43 -> A44 -> A45 -> A46 -> A47 -> A48 ->
    A49 -> A50 -> A51 -> A52 -> A53 -> A54 -> A55 -> A56 ->
    A57 -> A58 -> A59 -> A60 -> A61 -> A62 -> A63 -> A64 ->
    and64 A1 A2 A3 A4 A5 A6 A7 A8
          A9 A10 A11 A12 A13 A14 A15 A16
          A17 A18 A19 A20 A21 A22 A23 A24
          A25 A26 A27 A28 A29 A30 A31 A32
          A33 A34 A35 A36 A37 A38 A39 A40
          A41 A42 A43 A44 A45 A46 A47 A48
          A49 A50 A51 A52 A53 A54 A55 A56
          A57 A58 A59 A60 A61 A62 A63 A64.
Hint Constructors and64.

Lemma and64_intro (A1 A2 A3 A4 A5 A6 A7 A8
               A9 A10 A11 A12 A13 A14 A15 A16
               A17 A18 A19 A20 A21 A22 A23 A24
               A25 A26 A27 A28 A29 A30 A31 A32
               A33 A34 A35 A36 A37 A38 A39 A40
               A41 A42 A43 A44 A45 A46 A47 A48
               A49 A50 A51 A52 A53 A54 A55 A56
               A57 A58 A59 A60 A61 A62 A63 A64: Prop) :
  and64 A1 A2 A3 A4 A5 A6 A7 A8
        A9 A10 A11 A12 A13 A14 A15 A16
        A17 A18 A19 A20 A21 A22 A23 A24
        A25 A26 A27 A28 A29 A30 A31 A32
        A33 A34 A35 A36 A37 A38 A39 A40
        A41 A42 A43 A44 A45 A46 A47 A48
        A49 A50 A51 A52 A53 A54 A55 A56
        A57 A58 A59 A60 A61 A62 A63 A64 ->
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\
  A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\
  A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\
  A25 /\ A26 /\ A27 /\ A28 /\ A29 /\ A30 /\ A31 /\ A32 /\
  A33 /\ A34 /\ A35 /\ A36 /\ A37 /\ A38 /\ A39 /\ A40 /\
  A41 /\ A42 /\ A43 /\ A44 /\ A45 /\ A46 /\ A47 /\ A48 /\
  A49 /\ A50 /\ A51 /\ A52 /\ A53 /\ A54 /\ A55 /\ A56 /\
  A57 /\ A58 /\ A59 /\ A60 /\ A61 /\ A62 /\ A63 /\ A64.
Proof.
intro H. decompose record H. tauto.
Qed.

Inductive and96 (A1 A2 A3 A4 A5 A6 A7 A8
                 A9 A10 A11 A12 A13 A14 A15 A16
                 A17 A18 A19 A20 A21 A22 A23 A24
                 A25 A26 A27 A28 A29 A30 A31 A32
                 A33 A34 A35 A36 A37 A38 A39 A40
                 A41 A42 A43 A44 A45 A46 A47 A48
                 A49 A50 A51 A52 A53 A54 A55 A56
                 A57 A58 A59 A60 A61 A62 A63 A64
                 A65 A66 A67 A68 A69 A70 A71 A72
                 A73 A74 A75 A76 A77 A78 A79 A80
                 A81 A82 A83 A84 A85 A86 A87 A88
                 A89 A90 A91 A92 A93 A94 A95 A96 : Prop) : Prop :=
| conj96:
    A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 ->
    A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 ->
    A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 ->
    A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 ->
    A33 -> A34 -> A35 -> A36 -> A37 -> A38 -> A39 -> A40 ->
    A41 -> A42 -> A43 -> A44 -> A45 -> A46 -> A47 -> A48 ->
    A49 -> A50 -> A51 -> A52 -> A53 -> A54 -> A55 -> A56 ->
    A57 -> A58 -> A59 -> A60 -> A61 -> A62 -> A63 -> A64 ->
    A65 -> A66 -> A67 -> A68 -> A69 -> A70 -> A71 -> A72 ->
    A73 -> A74 -> A75 -> A76 -> A77 -> A78 -> A79 -> A80 ->
    A81 -> A82 -> A83 -> A84 -> A85 -> A86 -> A87 -> A88 ->
    A89 -> A90 -> A91 -> A92 -> A93 -> A94 -> A95 -> A96 ->
    and96 A1 A2 A3 A4 A5 A6 A7 A8
          A9 A10 A11 A12 A13 A14 A15 A16
          A17 A18 A19 A20 A21 A22 A23 A24
          A25 A26 A27 A28 A29 A30 A31 A32
          A33 A34 A35 A36 A37 A38 A39 A40
          A41 A42 A43 A44 A45 A46 A47 A48
          A49 A50 A51 A52 A53 A54 A55 A56
          A57 A58 A59 A60 A61 A62 A63 A64
          A65 A66 A67 A68 A69 A70 A71 A72
          A73 A74 A75 A76 A77 A78 A79 A80
          A81 A82 A83 A84 A85 A86 A87 A88
          A89 A90 A91 A92 A93 A94 A95 A96.
Hint Constructors and96.

Lemma and96_intro (A1 A2 A3 A4 A5 A6 A7 A8
                   A9 A10 A11 A12 A13 A14 A15 A16
                   A17 A18 A19 A20 A21 A22 A23 A24
                   A25 A26 A27 A28 A29 A30 A31 A32
                   A33 A34 A35 A36 A37 A38 A39 A40
                   A41 A42 A43 A44 A45 A46 A47 A48
                   A49 A50 A51 A52 A53 A54 A55 A56
                   A57 A58 A59 A60 A61 A62 A63 A64
                   A65 A66 A67 A68 A69 A70 A71 A72
                   A73 A74 A75 A76 A77 A78 A79 A80
                   A81 A82 A83 A84 A85 A86 A87 A88
                   A89 A90 A91 A92 A93 A94 A95 A96: Prop) :
  and96 A1 A2 A3 A4 A5 A6 A7 A8
        A9 A10 A11 A12 A13 A14 A15 A16
        A17 A18 A19 A20 A21 A22 A23 A24
        A25 A26 A27 A28 A29 A30 A31 A32
        A33 A34 A35 A36 A37 A38 A39 A40
        A41 A42 A43 A44 A45 A46 A47 A48
        A49 A50 A51 A52 A53 A54 A55 A56
        A57 A58 A59 A60 A61 A62 A63 A64
        A65 A66 A67 A68 A69 A70 A71 A72
        A73 A74 A75 A76 A77 A78 A79 A80
        A81 A82 A83 A84 A85 A86 A87 A88
        A89 A90 A91 A92 A93 A94 A95 A96 ->
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\
  A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\
  A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\
  A25 /\ A26 /\ A27 /\ A28 /\ A29 /\ A30 /\ A31 /\ A32 /\
  A33 /\ A34 /\ A35 /\ A36 /\ A37 /\ A38 /\ A39 /\ A40 /\
  A41 /\ A42 /\ A43 /\ A44 /\ A45 /\ A46 /\ A47 /\ A48 /\
  A49 /\ A50 /\ A51 /\ A52 /\ A53 /\ A54 /\ A55 /\ A56 /\
  A57 /\ A58 /\ A59 /\ A60 /\ A61 /\ A62 /\ A63 /\ A64 /\
  A65 /\ A66 /\ A67 /\ A68 /\ A69 /\ A70 /\ A71 /\ A72 /\
  A73 /\ A74 /\ A75 /\ A76 /\ A77 /\ A78 /\ A79 /\ A80 /\
  A81 /\ A82 /\ A83 /\ A84 /\ A85 /\ A86 /\ A87 /\ A88 /\
  A89 /\ A90 /\ A91 /\ A92 /\ A93 /\ A94 /\ A95 /\ A96.
Proof.
intro H. decompose record H. tauto.
Qed.

Ltac splits :=
  match goal with
    | |-   _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ =>
      apply and96_intro; apply conj96; splits
    | |-   _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ =>
      apply and64_intro; apply conj64; splits
    | |-   _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ =>
      apply and32_intro; apply conj32; splits
    | |-   _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ /\
           _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ =>
      apply and16_intro; apply conj16; splits
    | |-   _ /\ _  /\ _  /\ _ /\ _ /\ _  /\ _  /\ _ =>
      apply and8_intro; apply conj8; splits
    | |-   _ /\ _  /\ _  /\ _ => apply and4_1; apply conj4; splits
    | |-  (_ /\ _) /\ _  /\ _ => apply and4_2; apply conj4; splits
    | |-  (_ /\ _  /\ _) /\ _ => apply and4_3; apply conj4; splits
    | |- ((_ /\ _) /\ _) /\ _ => apply and4_4; apply conj4; splits
    | |- _ /\ _ => split; splits
    | _ => idtac
  end.

(** Version that does unfold definitions. *)
Ltac deep_splits :=
  match goal with
    | _ => split; deep_splits
    | _ => idtac
  end.

Module TestTactics.

Definition AND P Q := P /\ Q.

(* Testing splits *)
Goal forall (P:Prop), P -> (P /\ P) /\ (P /\ P).
intros P p.
splits. (* 4 goals *)
* trivial.
* trivial.
* trivial.
* trivial.
Qed.

Goal forall (P Q: Prop), P -> Q -> (AND P Q) /\ (P /\ Q).
intros P Q p q.
splits. (* 3 goals *)
* split; trivial.
* trivial.
* trivial.
Qed.

(* Testing deep_splits *)
Goal forall (P:Prop), P -> (P /\ P) /\ (P /\ P).
intros P p.
deep_splits; [trivial|trivial|trivial|trivial].
Qed.

Goal forall (P Q: Prop), P -> Q -> (AND P Q) /\ (P /\ Q).
intros P Q p q.
deep_splits. (* 4 goals *)
* trivial.
* trivial.
* trivial.
* trivial.
Qed.

End TestTactics.

(** * Useful Hints when dealing with [omega]. *)
Require Export Omega.
Hint Extern 3 (_ <= _) => first [omega | simpl; omega].
Hint Extern 3 (_ = _) => first [omega | simpl; omega].
Hint Extern 3 => exfalso; first [omega | simpl in *|-; omega].

(** Useful hints when dealing with equivalence relations. *)
Ltac equivalence_reflexivity :=
  match goal with
    | E: Equivalence ?R |- ?R _ _ => reflexivity
  end.
Hint Extern 3 => equivalence_reflexivity.
Hint Extern 3 (_ = _) => reflexivity.

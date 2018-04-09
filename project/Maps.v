(**
The standard library map defines notation that clashes with the step notation.
We'd rather keep the book notation.
*)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Strings.String.
Require Import Util.

Definition total_map (A:Type) := string -> A.
Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A := (fun _ => None).
Definition update {A:Type} (m: partial_map A) (x: string) (v: A) :=
  (fun x' => if string_beq x x' then Some v else m x').

Notation "m '&' { a --> x }" := 
  (update m a x) (at level 20).
Notation "m '&' { a --> x ; b --> y }" := 
  (update (m & { a --> x }) b y) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z }" := 
  (update (m & { a --> x ; b --> y }) c z) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t }" :=
  (update (m & { a --> x ; b --> y ; c --> z }) d t) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u }" :=
  (update (m & { a --> x ; b --> y ; c --> z ; d --> t }) e u) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }" :=
  (update (m & { a --> x ; b --> y ; c --> z ; d --> t ; e --> u }) f v) (at level 20).
   
Lemma partial_map_apply_empty : forall A x, (@empty A) x = None.
Proof.
  intros. unfold empty. reflexivity.
Qed.

Lemma partial_map_apply_eq : forall A (m: partial_map A) x v, (m & { x --> v }) x = Some v.
Proof.
  intros. unfold update. rewrite string_beq_refl. reflexivity.
Qed.

Lemma partial_map_apply_neq : forall (X:Type) (m: partial_map X) x1 x2 v,
  x1 <> x2 -> (m & { x1 --> v }) x2 = m x2.
Proof.
  intros. unfold update. rewrite (string_beq_false x1 x2 H). reflexivity.
Qed.

Lemma partial_map_update_same : forall X (m: partial_map X) x v,
  m x = Some v -> m & { x --> v } = m.
Proof.
  unfold update. intros. apply functional_extensionality. intros. destruct (string_beq x x0) eqn:res.
  - apply string_beq_true_iff in res. subst. rewrite H. reflexivity.
  - reflexivity.
Qed.

Theorem partial_map_update_permute : forall (X:Type) (m : partial_map X) v1 v2 x1 x2,
  x2 <> x1 -> m & { x1 --> v1; x2 --> v2} = m & { x2 --> v2; x1 --> v1 }.
Proof.
  unfold update. intros. apply functional_extensionality. intros.
  destruct (string_beq x1 x) eqn:res1.
  - destruct (string_beq x2 x) eqn:res2.
    + apply string_beq_true_iff in res1. apply string_beq_true_iff in res2. subst. contradiction.
    + reflexivity.
  - reflexivity.
Qed.

Lemma partial_map_update_shadow : forall A (m: partial_map A) v1 v2 x,
    m & { x --> v1 ; x --> v2 } = m & {x --> v2}.
Proof.
  unfold update. intros. apply functional_extensionality. intros.
  destruct (string_beq x x0); reflexivity.
Qed.
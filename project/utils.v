Require Export Coq.Strings.String.
Require Export Coq.Bool.Bool.

Definition string_beq x y := if string_dec x y then true else false.

Lemma string_beq_refl : forall s, string_beq s s = true.
Proof.
 intros s. unfold string_beq. destruct (string_dec s s).
 - reflexivity.
 - contradiction.
Qed.

Lemma string_beq_false : forall s s', s <> s' -> string_beq s s' = false.
Proof.
  intros. unfold string_beq. destruct (string_dec s s').
  - unfold not in H. rewrite e in H. contradiction.
  - reflexivity.
Qed.

Lemma string_beq_true_iff : forall x y : string,
  string_beq x y = true <-> x = y.
Proof.
   intros x y.
   unfold string_beq.
   destruct (string_dec x y) as [|Hs].
   - subst. split. reflexivity. reflexivity.
   - split.
     + intros contra. inversion contra.
     + intros H. inversion H. subst. destruct Hs. reflexivity.
Qed.

Lemma string_beq_false_iff : forall x y : string, string_beq x y = false <-> x <> y.
Proof.
  intros. rewrite <- string_beq_true_iff. rewrite not_true_iff_false. reflexivity.
Qed.

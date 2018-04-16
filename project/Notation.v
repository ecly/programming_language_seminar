Require Import Coq.Strings.String.

Require Import Maps.
Require Import Util.
Require Import Main.

Import STLC.

(* Normalize tactics for easy example proofs with multi_step. *)
Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | (instantiate; simpl)]);
  apply multi_refl.

Definition X : string := "X". Hint Unfold X.
Definition Y : string := "Y". Hint Unfold Y.
Definition Z : string := "Z". Hint Unfold Z.

Bind Scope notation_scope with term.

Notation "t1 ; t2" :=
  (t_app t1 t2) (at level 80, right associativity) : notation_scope.
Notation "( a \: T \-> t )" :=
  (t_abs a T t) (at level 80, right associativity) : notation_scope.
Notation "'ttrue'" :=
  t_true : notation_scope.
Notation "'ffalse'" :=
  t_false : notation_scope.
Notation "'IFB' b 'THEN' t1 'ELSE' t2" :=
  (t_if b t1 t2) (at level 80, right associativity) : notation_scope.
Notation "'LET' a \= t1 'IN' t2" :=
  (t_let a t1 t2) (at level 80, right associativity) : notation_scope.


(** The following declaration is needed to be able to use the
    notations in match patterns. *)
Open Scope notation_scope.

Definition abs_notation : term :=
  ( X \: TBool \-> ttrue ).

Example abs_notation_test :
  abs_notation = t_abs X TBool t_true.
Proof.
  unfold abs_notation. reflexivity.
Qed.

Definition ifb_notation : term :=
  IFB ttrue THEN ttrue ELSE ffalse.

Example ifb_notation_test :
  ifb_notation ==> t_true.
Proof.
  unfold ifb_notation. apply ST_IfTrue.
Qed.

Definition nested_ifb_notation : term :=
  IFB IFB ttrue THEN ffalse ELSE ttrue THEN ttrue ELSE ffalse.

Example nested_ifb_notation_test :
  nested_ifb_notation ==>* t_false.
Proof.
    unfold nested_ifb_notation. normalize. 
Qed.

Definition let_notation : term :=
  LET X \= t_true IN t_false.

Example let_notation_test :
  let_notation ==>* t_false.
Proof.
    unfold let_notation. normalize. 
Qed.

Definition test_notation_scope1 : term :=
  IFB ttrue THEN ffalse ELSE ttrue ; t_true.

Definition asd : term := t_abs "x" TBool t_true.
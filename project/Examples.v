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

Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation a := "a".
Notation f := "f".
Notation g := "g".
Notation l := "l".
Notation k := "k".
Notation i1 := "i1".
Notation i2 := "i2".
Notation processSum := "processSum".
Notation n := "n".
Notation eq := "eq".
Notation m := "m".
Notation evenodd := "evenodd".
Notation even := "even".
Notation odd := "odd".
Notation eo := "eo".

Definition fact :=
t_fix
  (t_abs f (TArrow TNat TNat)
    (t_abs a TNat
      (t_if
          (t_nat_eq (t_nat 0) (t_var a))
          (t_nat 1)
          (t_mult
            (t_var a)
            (t_app (t_var f) (t_pred (t_var a))))))).

Example fact_test:
(t_app fact (t_nat 4)) ==>* (t_nat 24).
Proof. unfold fact. normalize. Qed.

Definition Either a b :=
  TSCons "Left" a (TSCons "Right" b TSNil).

Definition either_case :=
  t_case_cons "Left" (t_abs "x"  TNat (t_var "x")) (t_case_one "Right" (t_abs "x" TBool (t_nat 0))).

Example either_test :
  t_match (t_sum "Right" t_true (Either TNat TBool)) either_case ==>* t_nat 0.
Proof.
  eapply multi_step.
  - eapply ST_MatchSumTail.
    + easy.
    + easy.
  - eapply multi_step.
    + eapply ST_AppAbs. apply v_true.
    + simpl. apply multi_refl.
Qed.

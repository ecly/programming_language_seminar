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
      (t_abs "x" TNat
        (t_if
          (t_nat_eq (t_nat 0) (t_var "x"))
          (t_nat 1)
          (t_mult
            (t_var "x")
            (t_app (t_var f) (t_pred (t_var "x"))))))).

Example fact_test:
  (t_app fact (t_nat 4)) ==>* (t_nat 24).
Proof. unfold fact. normalize. Qed.

Definition Either a b :=
  TSCons "Left" a (TSCons "Right" b TSNil).

Example either_test:
  t_match 
    (t_sum "Right" t_true (Either TNat TBool)) 
    (t_case_cons "Left" 
      (t_abs "x"  TNat (t_var "x")) 
      (t_case_one "Right" (t_abs "x" TBool (t_nat 0))))
        ==>* t_nat 0.
Proof.
  eapply multi_step.
  - apply ST_MatchSumTail; easy.
  - eapply multi_step.
    + apply ST_AppAbs. apply v_true.
    + apply multi_refl.
Qed.

Definition product :=
  t_fix
    (t_abs "f" (TArrow (TList TNat) (TNat))
      (t_abs "x" (TList TNat)
        (t_match (t_var "x") 
          (t_case_cons "cons"
            (t_abs "l" 
              (TRCons "head" TNat 
              	(TRCons "tail" (TList TNat) TRNil))
              (t_mult 
              	(t_proj (t_var "l") "head") 
                (t_app 
                  (t_var "f") 
                  (t_proj (t_var "l") "tail"))))
          (t_case_one "nil" (t_abs "_" TRNil (t_nat 1))))))).

Example list_test :
  t_app product (t_lcons (t_nat 3) 
    (t_lcons (t_nat 7) (t_lnil TNat))) 
      ==>* t_nat 21.
Proof.
  unfold product.
  eapply multi_step. auto.
  eapply multi_step. apply ST_AppAbs. auto.
  eapply multi_step. simpl. auto.
  eapply multi_step. apply ST_AppAbs. auto.
  eapply multi_step. apply ST_Mult1. { simpl. apply ST_ProjValue. auto. easy. }
  simpl. eapply multi_step. apply ST_Mult2. auto. auto.
  simpl. eapply multi_step. apply ST_Mult2. auto.
    { apply ST_App2. auto. apply ST_ProjValue. auto. easy. }
  eapply multi_step. apply ST_Mult2. auto. { apply ST_AppAbs. auto. }
  simpl. eapply multi_step. apply ST_Mult2. auto. { apply ST_MatchListCons. auto. }
  eapply multi_step. apply ST_Mult2. auto. { apply ST_AppAbs. auto. }
  simpl. eapply multi_step. apply ST_Mult2. auto. { apply ST_Mult1. apply ST_ProjValue. auto. easy. }
  eapply multi_step. apply ST_Mult2. auto. { apply ST_Mult2. auto. auto. }
  simpl. eapply multi_step. apply ST_Mult2. auto.
    { apply ST_Mult2. auto. apply ST_App2. auto. apply ST_ProjValue. auto. easy. } 
  eapply multi_step. apply ST_Mult2. auto. { apply ST_Mult2. auto. auto. }
  simpl. eapply multi_step. auto.
  normalize.
Qed.
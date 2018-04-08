Require Import Coq.Strings.String.

Require Import Maps.
Require Import Util.
Require Import Main.

Import STLC.

Notation idB :=
  (t_abs x TBool (t_var x)).

Notation idBB :=
  (t_abs x (TArrow TBool TBool) (t_var x)).

Notation idBBBB :=
  (t_abs x (TArrow (TArrow TBool TBool)
                      (TArrow TBool TBool))
    (t_var x)).

Notation k := (t_abs x TBool (t_abs y TBool (t_var x))).

Notation notB := (t_abs x TBool (t_if (t_var x) t_false t_true)).

Lemma step_example5 :
       t_app (t_app idBBBB idBB) idB
  ==>* idB.
Proof. 
  eapply multi_step.
    apply ST_App1. 
    apply ST_AppAbs. auto.
  eapply multi_step.
    apply ST_AppAbs. auto.
    simpl. apply multi_refl.
Qed.

(* normalize tactic as defined in Types.v from PLF *)

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | (instantiate; simpl)]);
  apply multi_refl.

(** **** Exercise: 2 stars (step_example5)  *)
(** Try to do this one both with and without [normalize]. *)
Lemma step_example5_with_normalize :
       t_app (t_app idBBBB idBB) idB
  ==>* idB.
Proof. normalize. Qed.

(** **** Exercise: 2 stars, optional (typing_example_2_full)  *)
(** Prove the same result without using [auto], [eauto], or
    [eapply] (or [...]). *)
Example typing_example_2_full :
  empty |-
    (t_abs x TBool
       (t_abs y (TArrow TBool TBool)
          (t_app (t_var y) (t_app (t_var y) (t_var x))))) \in
    (TArrow TBool (TArrow (TArrow TBool TBool) TBool)).
Proof.
  apply T_Abs.
  apply T_Abs.
  apply T_App with (T11 := TBool).
  apply T_Var. reflexivity.
  apply T_App with (T11 := TBool);
  apply T_Var; reflexivity.
Qed.

(** **** Exercise: 2 stars (typing_example_3)  *)
(** Formally prove the following typing derivation holds: *)
(** 
       empty |- \x:Bool->B. \y:Bool->Bool. \z:Bool.
                   y (x z)
             \in T.
*)
Example typing_example_3 :
  exists T,
    empty |-
      (t_abs x (TArrow TBool TBool)
         (t_abs y (TArrow TBool TBool)
            (t_abs z TBool
               (t_app (t_var y) (t_app (t_var x) (t_var z)))))) \in
      T.
Proof with auto.
  eexists.
  repeat apply T_Abs.
  apply T_App with (T11 := TBool).
  apply T_Var. reflexivity.
  apply T_App with (T11 := TBool);
  apply T_Var; reflexivity.
Qed.

Example typing_nonexample_1 :
  ~ exists T,
      empty |-
        (t_abs x TBool
            (t_abs y TBool
               (t_app (t_var x) (t_var y)))) \in
        T.
Proof.
  intros Hc. inversion Hc.
  (* The [clear] tactic is useful here for tidying away bits of
     the context that we're not going to need again. *)
  inversion H. subst. clear H.
  inversion H5. subst. clear H5.
  inversion H4. subst. clear H4.
  inversion H2. subst. clear H2.
  inversion H5. subst. clear H5.
  inversion H1.  Qed.

(** **** Exercise: 3 stars, optional (typing_nonexample_3)  *)
(** Another nonexamplei:

    ~ (exists S, exists T,
          empty |- \x:S. x x \in T).
*)
Example typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |-
          (t_abs x S
             (t_app (t_var x) (t_var x))) \in
          T).
Proof.
  intros Hc. inversion Hc.
  inversion H. subst. clear H.
  inversion H0. subst. clear H0.
  inversion H5. subst. clear H5.
  inversion H2. subst. clear H2.
  inversion H4. subst. clear H4.
  rewrite H1 in H2. inversion H2.
  induction T11. 
  - inversion H2. 
  - inversion H0. apply IHT11_1. 
    + rewrite <- H3. apply H1.
    + rewrite <- H3. apply H2.
    + rewrite <- H3. apply H0.
Qed.

Lemma progress_t_app : forall T t1 t2,
  empty |- t_app t1 t2 \in T ->
  (value t1 \/ exists t1', t1 ==> t1') ->
  (value t2 \/ exists t2', t2 ==> t2') ->
  exists t', t_app t1 t2 ==> t'.
Proof.
  intros. destruct H0.
  - destruct H1.
    + (* t1 and t2 are both values *)
      inversion H0. subst.
      * exists ([x0 := t2] t). apply ST_AppAbs. apply H1.
      * inversion H. subst. inversion H6.
      * inversion H. subst. inversion H6.
    + destruct H1. exists (t_app t1 x0). constructor; assumption.
  - (* t1 can step, t2 is a value *) 
    destruct H0. exists (t_app x0 t2). constructor. assumption.
Qed.

(*--- StlcProp Section ---*)
(** **** Exercise: 3 stars, advanced (progress_from_term_ind)  *)
(** Show that progress can also be proved by induction on terms
    instead of induction on typing derivations. *)

Theorem progress' : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.
Proof.
  intros t.
  induction t; intros T Ht; auto.
  - (* T_Var *)
    inversion Ht.  inversion H1.
  -  (* T_App *) 
    right. inversion Ht. subst.
    destruct IHt1 with (TArrow T11 T).
    + destruct IHt2 with (T11); assumption.
    + eapply progress_t_app. apply Ht. eapply IHt1. apply H2. eapply IHt2. apply H4.
    + eapply progress_t_app. apply Ht. eapply IHt1. apply H2. eapply IHt2. apply H4.
  - (* T_If *) 
    inversion Ht. subst. right. 
    destruct IHt1 with (T := TBool). apply H3.
    apply canonical_forms_bool in H3. destruct H3; subst.
    + eexists. apply ST_IfTrue.
    + eexists. apply ST_IfFalse.
    + apply H.
    + destruct H. eexists. apply ST_If. apply H.
Qed.
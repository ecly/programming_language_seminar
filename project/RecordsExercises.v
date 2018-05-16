Require Import Main.
Require Import Maps.
Require Import Util.
Import STLC.

Open Scope string_scope.
Notation a := "a".
Notation i1 := "i1".
Notation i2 := "i2".

Lemma typing_example : forall A B, well_formed_ty A -> well_formed_ty B ->
  empty |-
    (t_app (t_abs a (TRCons i1 (TArrow A A)
                      (TRCons i2 (TArrow B B)
                       TRNil))
              (t_proj (t_var a) i2))
            (t_rcons i1 (t_abs a A (t_var a))
            (t_rcons i2 (t_abs a B (t_var a))
             t_rnil))) \in
    (TArrow B B).
Proof.
  intros. eapply T_App.
  - apply T_Abs.
    + apply WFT_trcons.
      * apply WFT_arrow; assumption.
      * { apply WFT_trcons.
        - apply WFT_arrow; assumption.
        - apply WFT_trnil.
        - apply RT_Nil.
      } 
      * apply RT_Cons.
    + eapply T_Proj.
      * { apply T_Var.
        - apply partial_map_apply_eq.
        - eapply WFT_trcons.
          + apply WFT_arrow; assumption.
          + apply WFT_trcons.
            * apply WFT_arrow; assumption.
            * apply WFT_trnil.
            * apply RT_Nil.
          + apply RT_Cons.
      }
      * simpl. reflexivity.
  - apply T_RCons.
    + apply T_Abs. assumption. apply T_Var. apply partial_map_apply_eq. assumption.
    + apply T_RCons.
      * apply T_Abs. assumption. apply T_Var. apply partial_map_apply_eq. assumption.
      * apply T_RNil.
      * apply RT_Nil.
      * apply rt_nil.
    + apply RT_Cons.
    + apply rt_cons.
Qed.

Example typing_nonexample : forall A B, well_formed_ty A -> well_formed_ty B ->
  ~exists T,
      (update empty a (TRCons i2 (TArrow A A)
                                TRNil)) |-
               (t_rcons i1 (t_abs a B (t_var a)) (t_var a)) \in
               T.
Proof.
  intros. intros contra. destruct contra. inversion H1. subst. inversion H10.
Qed.
  
Example typing_nonexample_2 : forall A B y, well_formed_ty A -> well_formed_ty B ->
  ~ exists T,
    (update empty y A) |-
           (t_app (t_abs a (TRCons i1 A TRNil)
                     (t_proj (t_var a) i1))
                   (t_rcons i1 (t_var y) (t_rcons i2 (t_var y) t_rnil))) \in
           T.
Proof. (* Applied value has type {i1, i2}, expected {i1} *)
  intros. intros contra. destruct contra. inversion H1. subst.
  inversion H5. subst.
  inversion H7. subst.
  inversion H13.
Qed.
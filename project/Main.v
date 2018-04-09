Set Warnings "-notation-overridden".

Require Import Coq.Strings.String.

Require Import Maps.
Require Import Util.

Module STLC.

Inductive ty : Type  :=
  | TBool  : ty
  | TArrow : ty -> ty -> ty.

Inductive term : Type :=
  | t_var : string -> term
  | t_app : term -> term -> term
  | t_abs : string -> ty -> term -> term
  | t_true : term
  | t_false : term
  | t_if : term -> term -> term -> term.

(* Needed for string definitions *)  
Open Scope string_scope.

Definition x := "x". Hint Unfold x.
Definition y := "y". Hint Unfold y.
Definition z := "z". Hint Unfold z.

Inductive value : term -> Prop :=
  | v_abs : forall x T t,
      value (t_abs x T t)
  | v_true :
      value t_true
  | v_false :
      value t_false.
Hint Constructors value.


Reserved Notation "'[' x ':=' s ']' t" (at level 20).
Fixpoint subst (x:string) (s:term) (t:term) : term :=
  match t with
  | t_var x' =>
      if string_beq x x' then s else t
  | t_abs x' T t1 =>
      t_abs x' T (if string_beq x x' then t1 else ([x:=s] t1))
  | t_app t1 t2 =>
      t_app ([x:=s] t1) ([x:=s] t2)
  | t_true =>
      t_true
  | t_false =>
      t_false
  | t_if t1 t2 t3 =>
      t_if ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Inductive subst_ind (x:string) (s:term) : term -> term -> Prop :=
  | subst_var_eq : subst_ind x s (t_var x) s
  | subst_var_neq : forall x', x <> x' -> subst_ind x s (t_var x') (t_var x')
  | subst_app : forall t1 t1' t2 t2', subst_ind x s t1 t1' -> subst_ind x s t2 t2' -> 
     subst_ind x s (t_app t1 t2) (t_app t1' t2')
  | subst_abs_eq : forall T t, subst_ind x s (t_abs x T t) (t_abs x T t)
  | subst_abs_neq : forall x' T t t', x <> x' -> subst_ind x s t t' -> 
      subst_ind x s (t_abs x' T t) (t_abs x' T t')
  | subst_true : subst_ind x s t_true t_true
  | subst_false : subst_ind x s t_false t_false
  | subst_if : forall t1 t1' t2 t2' t3 t3', subst_ind x s t1 t1' -> subst_ind x s t2 t2' ->
      subst_ind x s t3 t3' -> subst_ind x s (t_if t1 t2 t3) (t_if t1' t2' t3').
Hint Constructors subst_ind.

 
Theorem subst_ind_correct : forall x s t t',
  [x:=s]t = t' <-> subst_ind x s t t'.
Proof.
  split.
  - generalize dependent x0. generalize dependent s. generalize dependent t'.
    induction t as [x'| |x'| | | ]; intros t' s x H; simpl in H.
    + destruct (string_beq x x') eqn:res.
      * rewrite string_beq_true_iff in res. subst. apply subst_var_eq.
      * rewrite <- H. apply subst_var_neq. apply string_beq_false_iff. apply res.
    + subst. apply subst_app.
      * apply IHt1. reflexivity.
      * apply IHt2. reflexivity.
    + destruct (string_beq x x') eqn:res.
      * rewrite string_beq_true_iff in res. subst. apply subst_abs_eq.
      * rewrite <- H. rewrite string_beq_false_iff in res. apply subst_abs_neq. 
        assumption. apply IHt. reflexivity.
    + rewrite <- H. apply subst_true.
    + rewrite <- H. apply subst_false.
    + rewrite <- H. apply subst_if; auto.
  - intros H. induction H; simpl.
    + rewrite string_beq_refl. reflexivity.
    + rewrite (string_beq_false x0 x' H). reflexivity.
    + subst. reflexivity.
    + rewrite string_beq_refl. reflexivity.
    + subst. rewrite (string_beq_false x0 x' H). reflexivity.
    + reflexivity.
    + reflexivity.
    + subst. reflexivity.
Qed.

Reserved Notation "t1 '==>' t2" (at level 40).
Inductive step : term -> term -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (t_app (t_abs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         t_app t1 t2 ==> t_app t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         t_app v1 t2 ==> t_app v1  t2'
  | ST_IfTrue : forall t1 t2,
      (t_if t_true t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (t_if t_false t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (t_if t1 t2 t3) ==> (t_if t1' t2 t3)

where "t1 '==>' t2" := (step t1 t2).
Hint Constructors step.

(* An arbitrary binary relation *)
Definition relation (X: Type) := X -> X -> Prop.
(* Defines the reflexivity and transitivity of the relations *)
Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl  : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
                    
Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

(** Typing *)
Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
Inductive has_type : context -> term -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- t_var x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      Gamma & {x --> T11} |- t12 \in T12 ->
      Gamma |- t_abs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 ->
      Gamma |- t2 \in T11 ->
      Gamma |- t_app t1 t2 \in T12
  | T_True : forall Gamma,
       Gamma |- t_true \in TBool
  | T_False : forall Gamma,
       Gamma |- t_false \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- t_if t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).
Hint Constructors has_type.

(** Lemmas stating the canonical form of boolean and arrow types *)
Lemma canonical_forms_bool : forall t,
  empty |- t \in TBool ->
  value t ->
  (t = t_true) \/ (t = t_false).
Proof.
  intros t HT HVal.
  inversion HVal; intros; subst; try inversion HT; auto.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (TArrow T1 T2) ->
  value t ->
  exists x u, t = t_abs x T1 u.
Proof.
  intros t T1 T2 HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  exists x0. exists t0.  auto.
Qed.

(** A well-typed term can always take a smallstep if it is not a value *)  
Theorem progress : forall t T,
  empty |- t \in T ->
  value t \/ exists t', t ==> t'.
Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  induction Ht; subst Gamma...
  - (* T_Var *)
    (* contradictory: variables cannot be typed in an
       empty context *)
    inversion H.
  - (* T_App *)
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a
       value or steps... *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct IHHt2...
      * (* t2 is also a value *)
        assert (exists x0 t0, t1 = t_abs x0 T11 t0).
        eapply canonical_forms_fun; eauto.
        destruct H1 as [x0 [t0 Heq]]. subst.
        exists ([x0:=t2]t0)...
      * (* t2 steps *)
        inversion H0 as [t2' Hstp]. exists (t_app t1 t2')...
    + (* t1 steps *)
      inversion H as [t1' Hstp]. exists (t_app t1' t2)...
  - (* T_If *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct (canonical_forms_bool t1); subst; eauto.
    + (* t1 also steps *)
      inversion H as [t1' Hstp]. exists (t_if t1' t2 t3)...
Qed.

(** Defines that a variable appears free in a term. *)  
Inductive appears_free_in : string -> term -> Prop :=
  | afi_var : forall x,
      appears_free_in x (t_var x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> 
      appears_free_in x (t_app t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> 
      appears_free_in x (t_app t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x  ->
      appears_free_in x t12 ->
      appears_free_in x (t_abs y T11 t12)
  | afi_if1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (t_if t1 t2 t3)
  | afi_if2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (t_if t1 t2 t3)
  | afi_if3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (t_if t1 t2 t3).
Hint Constructors appears_free_in.
  
(** A closed term is one that does not contain any free variables *)
Definition closed (t:term) :=
  forall x, ~ appears_free_in x t.

(** If there is a free variable in a well-typed term, it must exist in the context *)
Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof.
  intros x t T Gamma H H0. generalize dependent Gamma.
  generalize dependent T.
  induction H;
         intros; try solve [inversion H0; eauto].
  - (* afi_abs *)
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite partial_map_apply_neq in H7; assumption.
Qed. 

(** If a term is well-typed without any bound variables, it must be closed *)
Corollary typable_empty_closed : forall t T,
    empty |- t \in T  ->
    closed t.
Proof.
  unfold closed. intros t T H x H1. eapply free_in_context in H.
  - inversion H. inversion H0.
  - apply H1.
Qed.

(** A context can be swapped with another if they both bind all free variables in the same way *)
Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.
Proof with eauto.
  intros.
  generalize dependent Gamma'.
  induction H; intros; auto.
  - (* T_Var *)
    apply T_Var. rewrite <- H0...
  - (* T_Abs *)
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... the [Gamma'] we use to
       instantiate is [Gamma & {{x-->T11}}] *)
    unfold update. destruct (string_beq x0 x1) eqn: Hx0x1...
    rewrite string_beq_false_iff in Hx0x1. auto.
  - (* T_App *)
    apply T_App with T11...
Qed.

(** If a term has one time, it cannot have another *)
Lemma type_unique : forall t T U Gamma, Gamma |- t \in T -> Gamma |- t \in U -> T = U.
Proof.
  induction t; intros; inversion H; inversion H0; subst.
  - rewrite H3 in H7. inversion H7. reflexivity.
  - assert (T11 = T0). { eapply IHt2. apply H6. apply H12. } subst. 
    assert (TArrow T0 T = TArrow T0 U). { eapply IHt1. apply H4. apply H10. }
    inversion H1. reflexivity.
  - assert (T12 = T1). { eapply IHt. apply H6. apply H12. } subst. reflexivity.
  - reflexivity.
  - reflexivity.
  - eapply IHt2. apply H7. apply H15.
Qed.

(** If a variable has a type U in the context of t, t can be substituted by a value of type U. *)
Lemma substitution_preserves_typing : forall Gamma x U t v T,
  Gamma & {x-->U} |- t \in T ->
  empty |- v \in U   ->
  Gamma |- [x:=v]t \in T.
Proof with eauto.
  intros Gamma x U t v T H H1.
  generalize dependent Gamma. generalize dependent T.
  
  induction t; intros T Gamma H; inversion H; subst; simpl...
  - destruct (string_beqP x s).
    + subst. assert (Gamma & { s --> U} |- t_var s \in U). {
        apply T_Var. apply partial_map_apply_eq.
      }
      assert (T = U). { eapply type_unique. apply H. apply H0. } subst.
      eapply context_invariance in H1. apply H1. intros. apply typable_empty_closed in H1.
      unfold closed in H1. destruct (H1 x0). apply H2.
    + apply T_Var. rewrite partial_map_apply_neq in H3; assumption.
  - (* tabs *)
    rename s into y. rename t into T. apply T_Abs.
    destruct (string_beqP x y) as [Hxy | Hxy].
    + (* x=y *)
      subst. rewrite partial_map_update_shadow in H6. apply H6.
    + (* x<>y *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update.
      destruct (string_beqP y z) as [Hyz | Hyz]; subst; trivial.
      rewrite <- string_beq_false_iff in Hxy.
      rewrite Hxy...
Qed.

(** Taking a step preserves the type *)
Theorem preservation : forall t t' T,
  empty |- t \in T  ->
  t ==> t'  ->
  empty |- t' \in T.
Proof with eauto.
  remember (@empty ty) as Gamma.
  intros t t' T HT. generalize dependent t'.
  induction HT;
       intros t' HE; subst Gamma; subst;
       try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T11...
      inversion HT1...
Qed.

(** A normal form i a term that cannot step any further *)
Definition normal_form t : Prop := ~exists t', t ==> t'.

Definition stuck (t:term) : Prop :=
  (normal_form) t /\ ~ value t.
  
(** A well-typed term cannot be stuck *)
Corollary soundness : forall t t' T,
  empty |- t \in T ->
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.
  - destruct (progress x0 T Hhas_type); contradiction.
  - apply IHHmulti.
    + eapply preservation. apply Hhas_type. apply H.
    + apply Hnf.
    + apply Hnot_val.
Qed.
 
End STLC.
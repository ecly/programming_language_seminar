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
  
End STLC.
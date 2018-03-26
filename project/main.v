Require Import Coq.Strings.String.
Require Import utils.

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



End STLC.
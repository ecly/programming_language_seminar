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
  intros s x t t'. split.
  - intros H. induction t.
    + subst. destruct (string_dec s s0).
      * subst. simpl. simpl. rewrite string_beq_refl. apply subst_var_eq.
  (* FILL IN HERE *) Admitted.
  
End STLC.
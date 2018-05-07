Set Warnings "-notation-overridden".

Require Import Coq.Strings.String.

Require Import Maps.
Require Import Util.

Module STLC.

Inductive ty : Type  :=
  | TBool  : ty
  | TArrow : ty -> ty -> ty
  | TRNil : ty (* Empty record *)
  | TRCons : string -> ty -> ty -> ty (* Extend record *)
  | TSNil : ty (* Empty sum *)
  | TSCons : string -> ty -> ty -> ty (* Extend sum *).

Inductive term : Type :=
  | t_var : string -> term
  | t_app : term -> term -> term
  | t_abs : string -> ty -> term -> term
  | t_true : term
  | t_false : term
  | t_if : term -> term -> term -> term
  | t_let : string -> term -> term -> term (* let x:T = term in term *)
  | t_proj : term -> string -> term (* Field access on a record *)
  | t_rnil : term (* Empty record *)
  | t_rcons : string -> term -> term -> term (* Extend record *)
  | t_fix : term -> term
  | t_sum : string -> term -> ty -> term (* Create a sum type, needs type annotation *)
  | t_match : term -> case_list -> term (* Match sum type cases. Each term is a function. *)
  (* Cases cannot be in term, as we then have both valid and invalid untyped terms *)
with case_list : Type :=
  | t_case_one : string -> term -> case_list
  | t_case_cons : string -> term -> case_list -> case_list.
Scheme term_ind_rec := Induction for term Sort Set
with case_list_ind_rec := Induction for case_list Sort Set.

(* Needed for string definitions *)  
Open Scope string_scope.

(* Whether a type is a record type. *)
Inductive record_ty : ty -> Prop :=
  | RT_Nil : record_ty TRNil
  | RT_Cons : forall f T1 T2, record_ty (TRCons f T1 T2).
Hint Constructors record_ty.

(* Whether a type is a sum type *)
Inductive sum_ty : ty -> Prop :=
  | SumT_Nil : sum_ty TSNil
  | SumT_Cons : forall f T1 T2, sum_ty (TSCons f T1 T2).
Hint Constructors sum_ty.

(* Whether a type makes sense. 
   For example adding a record field to something that is not a record does not. *)
Inductive well_formed_ty : ty -> Prop :=
  | WFT_bool : well_formed_ty TBool
  | WFT_arrow : forall T1 T2, well_formed_ty T1 -> well_formed_ty T2 -> well_formed_ty (TArrow T1 T2)
  | WFT_trnil : well_formed_ty TRNil
  | WFT_trcons : forall s T1 T2,
      well_formed_ty T1 -> well_formed_ty T2 -> record_ty T2 -> well_formed_ty (TRCons s T1 T2)
  | WFT_tsnil : well_formed_ty TSNil
  | WFT_tscons : forall s T1 T2,
      well_formed_ty T1 -> well_formed_ty T2 -> sum_ty T2 -> well_formed_ty (TSCons s T1 T2).
Hint Constructors well_formed_ty.

(* Whether a term is a record *)
Inductive record_term : term -> Prop :=
  | rt_nil : record_term t_rnil
  | rt_cons : forall f t1 t2, record_term (t_rcons f t1 t2).

Inductive value : term -> Prop :=
  | v_abs : forall x T t,
      value (t_abs x T t)
  | v_true :
      value t_true
  | v_false :
      value t_false
  | v_rnil : value t_rnil
  | v_rcons : forall f t1 t2, value t1 -> value t2 -> value (t_rcons f t1 t2)
  | v_sum : forall s v T, value v -> value (t_sum s v T).
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
  | t_let x' t1 t2 => 
      t_let x' ([x:=s] t1) (if string_beq x x' then t2 else ([x:=s] t2))
  | t_proj t f => t_proj ([x:=s] t) f
  | t_rnil => t_rnil
  | t_rcons f t t_rst => t_rcons f ([x:=s] t) ([x:=s] t_rst)
  | t_fix t1 => 
      t_fix (subst x s t1)
  | t_sum x' t T => t_sum x' ([x:=s] t) T
  | t_match t hs => t_match ([x:=s]t) (subst_cases x s hs)
  end
with subst_cases x s cases :=
  match cases with
  | t_case_one x' h => t_case_one x' ([x:=s]h)
  | t_case_cons x' h hs => t_case_cons x' ([x:=s]h) (subst_cases x s hs)
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
      subst_ind x s t3 t3' -> subst_ind x s (t_if t1 t2 t3) (t_if t1' t2' t3')
  | subst_let_eq : forall t1 t1' t2, subst_ind x s t1 t1' ->
      subst_ind x s (t_let x t1 t2) (t_let x t1' t2)
  | subst_let_neq : forall x' t1 t1' t2 t2', x <> x' -> subst_ind x s t1 t1' -> subst_ind x s t2 t2' ->
      subst_ind x s (t_let x' t1 t2) (t_let x' t1' t2')
  | subst_proj : forall f t t', subst_ind x s t t' -> subst_ind x s (t_proj t f) (t_proj t' f)
  | subst_rnil : subst_ind x s t_rnil t_rnil
  | subst_rcons : forall f t1 t1' t2 t2', subst_ind x s t1 t1' -> subst_ind x s t2 t2' -> 
      subst_ind x s (t_rcons f t1 t2) (t_rcons f t1' t2')
  | subst_fix : forall t1 t1', subst_ind x s t1 t1' -> subst_ind x s (t_fix t1) (t_fix t1')
  | subst_sum : forall x' t t' T, subst_ind x s t t' -> 
      subst_ind x s (t_sum x' t T) (t_sum x' t' T)
  | subst_match : forall t t' hs hs',
      subst_ind x s t t' ->
      subst_case_ind x s hs hs' ->
      subst_ind x s (t_match t hs) (t_match t' hs')
with subst_case_ind (x:string) (s:term) : case_list -> case_list -> Prop :=
  | subst_case_one : forall x' h h',
      subst_ind x s h h' ->
      subst_case_ind x s (t_case_one x' h) (t_case_one x' h')
  | subst_case_cons : forall x' h h' hs hs',
      subst_ind x s h h' ->
      subst_case_ind x s hs hs' ->
      subst_case_ind x s (t_case_cons x' h hs) (t_case_cons x' h' hs').
Scheme subst_ind_ind_rec := Induction for subst_ind Sort Prop
with subst_case_ind_ind_rec := Induction for subst_case_ind Sort Prop.
Hint Constructors subst_ind.
Hint Constructors subst_case_ind.
 
Theorem subst_ind_correct : forall x s t t',
  [x:=s]t = t' <-> subst_ind x s t t'.
Proof.
  split.
  - generalize dependent x. generalize dependent s. generalize dependent t'.
    induction t using term_ind_rec with
      (P := fun t => forall (t' s : term) (x : string), [x := s] t = t' -> subst_ind x s t t')
      (P0 := fun t => forall (t' : case_list) (s : term) (x : string),
        subst_cases x s t = t' -> subst_case_ind x s t t'); intros; subst; simpl.
    + destruct (string_beq x s) eqn:res.
      * rewrite string_beq_true_iff in res. subst. apply subst_var_eq.
      * apply subst_var_neq. apply string_beq_false_iff. apply res.
    + apply subst_app.
      * apply IHt1. reflexivity.
      * apply IHt2. reflexivity.
    + destruct (string_beq x s) eqn:res.
      * rewrite string_beq_true_iff in res. subst. apply subst_abs_eq.
      * rewrite string_beq_false_iff in res. apply subst_abs_neq. 
        assumption. apply IHt. reflexivity.
    + apply subst_true.
    + apply subst_false.
    + apply subst_if; auto.
    + destruct (string_beq x s) eqn:res.
      * rewrite string_beq_true_iff in res. subst. apply subst_let_eq. apply IHt1. reflexivity.
      * rewrite string_beq_false_iff in res. {
        apply subst_let_neq. 
        - apply res.
        - apply IHt1. reflexivity.
        - apply IHt2. reflexivity.
      } 
    + apply subst_proj. apply IHt. reflexivity.
    + apply subst_rnil.
    + apply subst_rcons.
      * apply IHt1. reflexivity.
      * apply IHt2. reflexivity.
    + apply subst_fix. apply IHt. reflexivity.  
    + apply subst_sum. apply IHt. reflexivity.
    + apply subst_match.
      * apply IHt. reflexivity.
      * apply IHt0. reflexivity.
    + apply subst_case_one. apply IHt. reflexivity.
    + apply subst_case_cons.
      * apply IHt. reflexivity.
      * apply IHt0. reflexivity.
  - intros H. induction H using subst_ind_ind_rec with
    (P := fun t t' H => [x := s] t = t')
    (P0 := fun hs hs' H => subst_cases x s hs = hs');
    simpl; subst; try reflexivity.
    + rewrite string_beq_refl. reflexivity.
    + rewrite string_beq_false. reflexivity. assumption.
    + rewrite string_beq_refl. reflexivity.
    + rewrite string_beq_false. subst. reflexivity. assumption.
    + rewrite string_beq_refl. subst. reflexivity.
    + rewrite string_beq_false. subst. reflexivity. assumption.
Qed.

(* Lookup a field in a record *)
Fixpoint trlookup f tr :=
  match tr with
  | t_rcons f' t tr' => if string_beq f f' then Some t else trlookup f tr'
  | _ => None
  end.

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
  | ST_Let : forall x t1 t1' t2, t1 ==> t1' -> (t_let x t1 t2) ==> (t_let x t1' t2)
  | ST_LetValue : forall x v1 t2, value v1 -> (t_let x v1 t2) ==> [x:=v1]t2
  | ST_Proj : forall t t' f, t ==> t' -> (t_proj t f) ==> (t_proj t' f)
  | ST_ProjValue : forall r f v, value r -> trlookup f r = Some v -> (t_proj r f) ==> v 
  | ST_RecordHead : forall t t' trest f, t ==> t' -> (t_rcons f t trest) ==> (t_rcons f t' trest)
  | ST_RecordTail : forall v f trest trest', value v -> trest ==> trest' -> 
      t_rcons f v trest ==> t_rcons f v trest'
  | ST_Fix1 : forall t1 t1', t1 ==> t1' -> t_fix t1 ==> t_fix t1'
  | ST_FixAbs : forall x T t1, t_fix (t_abs x T t1) ==> [x:=t_fix(t_abs x T t1)]t1
  | ST_Sum : forall x t t' T, t ==> t' -> t_sum x t T ==> t_sum x t' T
  | ST_Match : forall t t' hs, t ==> t' -> t_match t hs ==> t_match t' hs
  | ST_MatchSumOne : forall x t t' T, t_match (t_sum x t T) (t_case_one x t') ==> t_app t' t
  | ST_MatchSumHead : forall x t t' hs T, t_match (t_sum x t T) (t_case_cons x t' hs) ==> t_app t' t
  | ST_MatchSumTail : forall x x' t t' t'' hs T TS,
      x <> x' ->
      t_match (t_sum x t TS) hs ==> t_app t' t ->
      t_match (t_sum x t (TSCons x' T TS)) (t_case_cons x' t'' hs) ==> t_app t' t
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

(* Lookup the type of a field in a record *)
Fixpoint TRlookup f tr :=
  match tr with
  | TRCons f' T Trest => if string_beq f f' then Some T else TRlookup f Trest
  | _ => None
  end.
  
(* If a record type is well formed, all contained values are as well *)
Lemma wellformed_record_lookup : forall f T Tf,
  well_formed_ty T ->
  TRlookup f T = Some Tf ->
  well_formed_ty Tf.
Proof.
  intros f T. induction T; intros; try easy.
  inversion H. subst. unfold TRlookup in H0.
  destruct (string_beq f s); try eauto.
  inversion H0. subst. apply H4.
Qed.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
Inductive has_type : context -> term -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      well_formed_ty T ->
      Gamma |- t_var x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      well_formed_ty T11 ->
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
  | T_Let : forall Gamma x t1 T1 t2 T,
      Gamma |- t1 \in T1 ->
      Gamma & {x --> T1} |- t2 \in T ->
      Gamma |- t_let x t1 t2 \in T
  | T_Proj : forall Gamma t f TR T,
      Gamma |- t \in TR ->
      TRlookup f TR = Some T ->
      Gamma |- t_proj t f \in T
  | T_RNil : forall Gamma,
      Gamma |- t_rnil \in TRNil
  | T_RCons : forall Gamma f t tr T Trest ,
      Gamma |- t \in T ->
      Gamma |- tr \in Trest ->
      record_ty Trest ->
      record_term tr ->
      Gamma |- t_rcons f t tr \in TRCons f T Trest
  | T_Fix : forall Gamma t1 T1,
      Gamma |- t1 \in TArrow T1 T1 ->
      Gamma |- t_fix t1 \in T1
  | T_SumEq : forall Gamma t T T2 x,
      Gamma |- t \in T ->
      sum_ty T2 ->
      well_formed_ty T2 ->
      Gamma |- t_sum x t (TSCons x T T2) \in (TSCons x T T2)
  (* Can always add more cases *)
  | T_SumNeq : forall Gamma t T TR x x',
      Gamma |- t_sum x t TR \in TR -> 
      x <> x' ->
      well_formed_ty T ->
      Gamma |- t_sum x t (TSCons x' T TR) \in (TSCons x' T TR)
  | T_Match : forall Gamma x t hs T T' TR,
      Gamma |- t \in TSCons x T' TR ->
      match_has_type Gamma (TSCons x T' TR) hs T ->
      Gamma |- t_match t hs \in T
(* Whether a match on a sum type has the given type *)
with match_has_type : context -> ty -> case_list -> ty -> Prop :=
  | T_CaseOne : forall Gamma x t T T',
      Gamma |- t \in TArrow T' T ->
      match_has_type Gamma (TSCons x T' TSNil) (t_case_one x t) T
  | T_CaseCons : forall Gamma x t hs T T' TR,
      Gamma |- t \in TArrow T' T ->
      match_has_type Gamma TR hs T ->
      match_has_type Gamma (TSCons x T' TR) (t_case_cons x t hs) T
where "Gamma '|-' t '\in' T" := (has_type Gamma t T).
Scheme has_type_ind_rec := Induction for has_type Sort Prop
with match_has_type_ind_rec := Induction for match_has_type Sort Prop.
Hint Constructors has_type.

Lemma sum_val_has_type : forall Gamma x t T, Gamma |- t_sum x t T \in T -> exists T', Gamma |- t \in T'.
Proof.
  intros. remember (t_sum x t T). induction H; intros; try congruence; inversion Heqt0; subst.
  - exists T. assumption.
  - apply IHhas_type. reflexivity.
Qed.

(* If has_type t T, then T is well formed *)
Lemma has_type_wellformed : forall Gamma t T, Gamma |- t \in T -> well_formed_ty T.
Proof.
  intros. induction H using has_type_ind_rec with
    (P := fun Gamma t T H => well_formed_ty T)
    (P0 := fun Gamma TR hs T H => well_formed_ty T);
    try eauto.
  - inversion IHhas_type1. assumption.
  - eapply wellformed_record_lookup. apply IHhas_type. apply e.
  - inversion IHhas_type. apply H2.
  - constructor; try assumption. inversion H; constructor.
  - inversion IHhas_type; subst. assumption.
Qed.

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
  exists x. exists t0.  auto.
Qed.

Lemma step_preserves_record_term : forall t t',
  record_term t ->
  t ==> t' ->
  record_term t'.
Proof.
  intros. inversion H; subst.
  - inversion H0.
  - inversion H0; subst; apply rt_cons.
Qed.

(* If looking up a field in a record type returns a type, then looking up a field in a record gives
   a value of that type. *)
Lemma lookup_matches : forall v f T Tf,
  value v ->
  empty |- v \in T ->
  TRlookup f T = Some Tf ->
  exists t, trlookup f v = Some t /\ empty |- t \in Tf.
Proof.
  intros v f T Ti Hval Htyp Hget.
  remember (@empty ty) as Gamma.
  induction Htyp; subst; try easy.
  - simpl in Hget. simpl. destruct (string_beq f f0).
    + simpl. inversion Hget. subst. exists t. eauto.
    + destruct IHHtyp2 as [vi [Hgeti Htypi]]; eauto. inversion Hval. eauto.
Qed.

(** A well-typed term can always take a smallstep if it is not a value *)  
Theorem progress : forall t T,
  empty |- t \in T ->
  value t \/ exists t', t ==> t'.
Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  induction Ht using has_type_ind_rec with
    (P := fun Gamma t T Ht => Gamma = empty -> value t \/ (exists t', t ==> t'))
    (P0 := fun Gamma TS hs T Ht => Gamma = empty ->
      forall x t, Gamma |- t_sum x t TS \in TS -> match_has_type Gamma TS hs T ->
      exists t', t_match (t_sum x t TS) hs ==> t_app t' t);
    subst; try rename e into H. try rename w into H0.
  - (* T_Var *)
    (* contradictory: variables cannot be typed in an
       empty context *)
    inversion H.
  - auto.
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
  - auto.
  - auto.
  - (* T_If *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct (canonical_forms_bool t1); subst; eauto.
    + (* t1 also steps *)
      inversion H as [t1' Hstp]. exists (t_if t1' t2 t3)...
  - (* T_Let *)
    right. destruct IHHt1... destruct H. exists (t_let x x0 t2). apply ST_Let. apply H.
  - (* T_Proj *)
    right. destruct IHHt; try easy.
    + destruct (lookup_matches t f TR T H0 Ht H). exists x. destruct H1.
      apply ST_ProjValue. apply H0. apply H1.
    + destruct H0. exists (t_proj x f). apply ST_Proj. apply H0.
  - (* T_RNil *) left. constructor.
  - (* T_RCons *)
    destruct IHHt1; try easy.
    + destruct IHHt2; try easy.
      * left. eauto.
      * right. destruct H0. exists (t_rcons f t x). apply ST_RecordTail; assumption.
    + right. destruct H. exists (t_rcons f x tr). apply ST_RecordHead. assumption. 
  - (* T_Fix *)
    right. destruct IHHt...
    inversion H; subst; try easy...
    inversion H...
  - (* T_SumEq *)
    destruct IHHt; try reflexivity.
    + left. constructor. assumption.
    + right. destruct H. exists (t_sum x x0 (TSCons x T T2)). constructor. assumption.
  - (* T_SumNeq *) destruct IHHt; try reflexivity.
    + left. constructor. inversion H. subst. assumption.
    + right. destruct H. inversion H. subst.
      exists (t_sum x t' (TSCons x' T TR)). constructor. assumption.
  - (* T_Match *)
    right. destruct IHHt; eauto.
    + inversion Ht; subst; try easy.
      * {
        inversion m; subst.
        - exists (t_app t t0). apply ST_MatchSumOne.
        - exists (t_app t t0). apply ST_MatchSumHead.
        }
      * inversion m; subst. inversion H5. {
        edestruct IHHt0; auto.
        - apply Ht.
        - exists (t_app x1 t0). apply H0.
        }
    + destruct H. exists (t_match x0 hs). constructor. assumption.
  - intros. inversion H; subst.
    + exists t. apply ST_MatchSumOne.
    + inversion H5.
  - intros. inversion H; subst.
    + exists t. constructor.
    + edestruct IHHt0. reflexivity. apply H5. apply m. exists x1. apply ST_MatchSumTail. assumption.
      assumption.
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
      appears_free_in x (t_if t1 t2 t3)
  | afi_let1 : forall x y t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (t_let y t1 t2)
  | afi_let2 : forall x y t1 t2,
      y <> x ->
      appears_free_in x t2 ->
      appears_free_in x (t_let y t1 t2)
  | afi_proj : forall x t f,
      appears_free_in x t ->
      appears_free_in x (t_proj t f)
  | afi_rcons_head : forall x f t tr,
      appears_free_in x t ->
      appears_free_in x (t_rcons f t tr)
  | afi_rcons_tail : forall x f t tr,
      appears_free_in x tr ->
      appears_free_in x (t_rcons f t tr)
  | afi_fix : forall x t1,
      appears_free_in x t1 ->
      appears_free_in x (t_fix t1)
  | afi_sum : forall x x' t T, appears_free_in x t -> appears_free_in x (t_sum x' t T)
  | afi_match_t : forall x t hs, appears_free_in x t -> appears_free_in x (t_match t hs)
  | afi_match_hs : forall x t hs, appears_free_in_case_list x hs -> appears_free_in x (t_match t hs)
with appears_free_in_case_list : string -> case_list -> Prop :=
  | afi_cl_one : forall x x' h, appears_free_in x h -> appears_free_in_case_list x (t_case_one x' h)
  | afi_cl_cons_head : forall x x' h hs,
      appears_free_in x h ->
      appears_free_in_case_list x (t_case_cons x' h hs)
  | afi_cl_cons_tail : forall x x' h hs,
      appears_free_in_case_list x hs ->
      appears_free_in_case_list x (t_case_cons x' h hs).
Scheme appears_free_in_ind_rec := Induction for appears_free_in Sort Prop
with appears_free_in_case_list_ind_rec := Induction for appears_free_in_case_list Sort Prop.
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
  induction H using appears_free_in_ind_rec with
    (P := fun x t H => forall T Gamma, Gamma |- t \in T -> exists T', Gamma x = Some T')
    (P0 := fun x hs H => forall T T'' Gamma, match_has_type Gamma T'' hs T -> exists T', Gamma x = Some T');
    intros; try solve [inversion H0; eauto].
  - (* afi_var *)
    inversion H; subst. exists T. assumption.
  - (* afi_abs *)
    inversion H0; subst.
    apply IHappears_free_in in H7.
    rewrite partial_map_apply_neq in H7; assumption.
  - inversion H0; subst. apply IHappears_free_in in H7.
    rewrite partial_map_apply_neq in H7; assumption.
  - (* afi_sum *)
    inversion H0; subst.
    + eapply IHappears_free_in. apply H5.
    + apply sum_val_has_type in H5. destruct H5. eapply IHappears_free_in. apply H1.
  - (* afi_match_hs_one *) 
    inversion H; subst. eapply IHappears_free_in. apply H5.
  - inversion H; subst. eapply IHappears_free_in. apply H7.
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
  induction H using has_type_ind_rec with
    (P := fun Gamma t T H => 
      forall Gamma', (forall x, appears_free_in x t -> Gamma x = Gamma' x) -> Gamma' |- t \in T)
    (P0 := fun Gamma T' t T H =>
      forall Gamma', (forall x, appears_free_in_case_list x t -> Gamma x = Gamma' x) -> match_has_type Gamma' T' t T); intros; auto.
  - (* T_Var *)
    apply T_Var. rewrite <- H; eauto. assumption.
  - (* T_Abs *)
    apply T_Abs. assumption. apply IHhas_type. intros.
    unfold update. destruct (string_beq x x0) eqn: Hx0x1...
    rewrite string_beq_false_iff in Hx0x1. auto.
  - (* T_App *)
    apply T_App with T11...
  - (* T_Let *)
    eapply T_Let with T1.
    + apply IHhas_type1. intros. apply H1. apply afi_let1. apply H2.
    + apply IHhas_type2. intros. destruct (string_beq x x0) eqn:res.
      * rewrite string_beq_true_iff in res. subst. repeat rewrite partial_map_apply_eq. reflexivity.
      * rewrite string_beq_false_iff in res. repeat rewrite partial_map_apply_neq; try assumption.
        apply H1. apply afi_let2; assumption.
  - (* T_Proj *)
    eapply T_Proj; eauto.
  - (* T_SumNeq *)
    apply T_SumNeq.
    + apply IHhas_type. intros. apply H0. inversion H1. apply afi_sum. assumption.
    + assumption.
    + assumption.
  - eapply T_Match.
    + apply IHhas_type. intros. apply H0. apply afi_match_t. assumption.
    + apply IHhas_type0. intros. apply H0. apply afi_match_hs. assumption.
  - apply T_CaseOne. apply IHhas_type. intros. apply H0. apply afi_cl_one. assumption.
  - apply T_CaseCons. apply IHhas_type. intros.
    + apply H0. apply afi_cl_cons_head. assumption.
    + apply IHhas_type0. intros. apply H0. apply afi_cl_cons_tail. assumption.
Qed.

(** If a term has one type, it cannot have another *)
Lemma type_unique : forall t T U Gamma, Gamma |- t \in T -> Gamma |- t \in U -> T = U.
Proof.
  induction t using term_ind_rec with
    (P := fun t => forall T U Gamma, Gamma |- t \in T -> Gamma |- t \in U -> T = U)
    (P0 := fun hs => forall T T' U Gamma,
      match_has_type Gamma T' hs T -> match_has_type Gamma T' hs U -> T = U);
  intros; inversion H; inversion H0; subst.
  - rewrite H2 in H7. inversion H7. reflexivity.
  - assert (T11 = T0). { eapply IHt2. apply H6. apply H12. } subst. 
    assert (TArrow T0 T = TArrow T0 U). { eapply IHt1. apply H4. apply H10. }
    inversion H1. reflexivity.
  - assert (T12 = T1). { eapply IHt. apply H7. apply H14. } subst. reflexivity.
  - reflexivity.
  - reflexivity.
  - eapply IHt2. apply H7. apply H15.
  - (* T_Let *) assert (T1 = T2). { eapply IHt1. apply H6. apply H13. } subst.
    eapply IHt2. apply H7. apply H14.
  - (* T_Proj *) assert (TR = TR0). { eapply IHt. apply H4. apply H10. } subst.
    rewrite H6 in H12. inversion H12. reflexivity.
  - (* T_RNil *) reflexivity.
  - (* T_RCons *)
    assert (Trest = Trest0). { eapply IHt2. apply H6. apply H15. }
    assert (T0 = T1). { eapply IHt1. apply H4. apply H13. }
    subst. reflexivity.
  - (* T_Fix *) assert (TArrow T T = TArrow U U). {eapply IHt. apply H3. apply H7. }
    inversion H1. reflexivity.
  - inversion H11. subst. reflexivity.
  - inversion H11. subst. reflexivity.
  - inversion H11. subst. reflexivity.
  - inversion H11. subst. reflexivity.
  - eapply IHt0. 
    + apply H6. 
    + assert (TSCons x T' TR = TSCons x0 T'0 TR0). { eapply IHt. apply H4. apply H10. } 
      inversion H1; subst. apply H12.
  - assert (TArrow T'0 T = TArrow T'1 U). { eapply IHt. apply H6. apply H12. } inversion H1. reflexivity.
  - assert (TArrow T'0 T = TArrow T'1 U). { eapply IHt. apply H7. apply H15. } inversion H1. reflexivity.
Qed.

(** If a variable has a type U in the context of t, t can be substituted by a value of type U. *)
Lemma substitution_preserves_typing : forall Gamma x U t v T,
  Gamma & {x-->U} |- t \in T ->
  empty |- v \in U   ->
  Gamma |- [x:=v]t \in T.
Proof with eauto.
  intros Gamma x U t v T H H1.
  generalize dependent Gamma. generalize dependent T.
  induction t using term_ind_rec with
    (P := fun t => forall T Gamma, Gamma & {x --> U} |- t \in T -> Gamma |- [x := v] t \in T)
    (P0 := fun hs => forall T T' Gamma,
      match_has_type (Gamma & {x --> U}) T' hs T -> match_has_type Gamma T' (subst_cases x v hs) T);
    intros; inversion H; subst; simpl; eauto.
  - destruct (string_beqP x s).
    + subst. assert (Gamma & { s --> U} |- t_var s \in U). {
        apply T_Var.
        - apply partial_map_apply_eq.
        - eapply has_type_wellformed. apply H1.
      }
      assert (T = U). { eapply type_unique. apply H. apply H0. } subst.
      eapply context_invariance in H1. apply H1. intros. apply typable_empty_closed in H1.
      unfold closed in H1. destruct (H1 x). apply H3.
    + apply T_Var; eauto. rewrite partial_map_apply_neq in H2; assumption.
  - (* tabs *)
    rename s into y. rename t into T. apply T_Abs; try assumption.
    destruct (string_beqP x y) as [Hxy | Hxy].
    + (* x=y *)
      subst. rewrite partial_map_update_shadow in H7. apply H7.
    + (* x<>y *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update.
      destruct (string_beqP y z) as [Hyz | Hyz]; subst; trivial.
      rewrite <- string_beq_false_iff in Hxy.
      rewrite Hxy...
  - (* t_let *) eapply T_Let. 
    + apply IHt1. apply H6. 
    + destruct (string_beqP x s).
      * subst. rewrite partial_map_update_shadow in H7. apply H7.
      * apply IHt2. rewrite partial_map_update_permute; assumption.
  - (* t_rcons *) apply T_RCons; eauto.
    inversion H9.
      + simpl. apply rt_nil.
      + simpl. apply rt_cons.   
  - (* T_SumNeq *)
    apply T_SumNeq; try assumption.
    induction TR; try easy.
    destruct (string_beq s s0) eqn:res.
    + rewrite string_beq_true_iff in res. subst. inversion H5; subst; try easy.
      apply T_SumEq; try assumption. apply IHt. assumption.
    + rewrite string_beq_false_iff in res. inversion H5; subst; try easy. 
      apply T_SumNeq; try assumption. apply IHTR2.
      * apply T_SumNeq; try assumption.
      * assumption.
  - apply T_CaseOne. apply IHt. assumption.
  - apply T_CaseCons.
    + apply IHt. assumption.
    + apply IHt0. assumption.
Qed.

Fixpoint find_case (hs : case_list) (x : string) : option term :=
  match hs with
  | t_case_one x' t => if string_beq x x' then Some t else None
  | t_case_cons x' t xs => if string_beq x x' then Some t else find_case xs x
  end.
  
Lemma step_implies_case_exists : forall hs x t t' TR,
  t_match (t_sum x t TR) hs ==> t_app t' t ->
  find_case hs x = Some t'.
Proof.
  induction hs; simpl; intros.
  - inversion H; subst. rewrite string_beq_refl. reflexivity.
  - inversion H; subst.
    + rewrite string_beq_refl. reflexivity.
    + rewrite string_beq_false. eapply IHhs. apply H8. apply H2.
Qed.
  
(** Taking a step preserves the type *)
Theorem preservation : forall t t' T,
  empty |- t \in T  ->
  t ==> t'  ->
  empty |- t' \in T.
Proof with eauto.
  remember (@empty ty) as Gamma.
  intros t t' T HT. generalize dependent t'.
  induction HT using has_type_ind_rec with
    (P := fun Gamma t T HT => Gamma = empty -> forall t', t ==> t' -> Gamma |- t' \in T)
    (P0 := fun Gamma TS hs T HT => Gamma = empty -> forall x t h,
      t_match (t_sum x t TS) hs ==> t_app h t -> Gamma |- (t_sum x t TS) \in TS ->
      match_has_type Gamma TS hs T ->
      find_case hs x = Some h ->
      Gamma |- t_app h t \in T);
     try intros lt' HE; intros; try subst Gamma; subst; try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T11...
      inversion HT1...
  - (* T_Let *)
    inversion HE; subst.
    + eapply T_Let.
      * apply IHHT1. reflexivity. apply H3.
      * apply HT2.
    + eapply substitution_preserves_typing. apply HT2. apply HT1.
  - (* T_Proj *)
    inversion HE; subst.
    + eapply T_Proj. apply IHHT. reflexivity. apply H2. apply e.
    + destruct (lookup_matches t f TR T H1 HT e). destruct H.
      assert (Some lt' = Some x). { rewrite <- H3. rewrite <- H. reflexivity. }
      inversion H2. subst. apply H0.
  - (* T_RCons *) inversion HE; subst; apply T_RCons; eauto.
    eapply step_preserves_record_term. apply r0. apply H4.
  -  (* T_Fix *) 
    inversion HE; subst; eauto.
    + inversion HT. subst. eapply substitution_preserves_typing.
      * apply H6.
      * apply T_Fix. apply HT.    
  - (* T_Match *)
    inversion HE; subst.
    + eapply T_Match. apply IHHT; auto. assumption.
    + inversion m; subst. eapply T_App. apply H6. inversion HT; subst. apply H4. contradiction.
    + inversion m; subst. eapply T_App. apply H7. inversion HT; subst. apply H4. contradiction.
    + inversion HT; subst. contradiction.
      eapply IHHT0; eauto. eapply step_implies_case_exists. apply HE.
  - inversion H2. inversion H0; subst.
    + eapply T_App. rewrite string_beq_refl in H4. inversion H4. subst.
      apply HT. apply H8.
    + rewrite string_beq_false in H4. inversion H4. assumption.
  - inversion H; subst.
    + eapply T_App. apply HT. inversion H0; subst. apply H7. contradiction.
    + eapply IHHT0; eauto.
      * inversion H0; subst. contradiction. apply H8.
      * inversion H2. rewrite (string_beq_false). reflexivity. assumption.
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
  - destruct (progress x T Hhas_type); contradiction.
  - apply IHHmulti.
    + eapply preservation. apply Hhas_type. apply H.
    + apply Hnf.
    + apply Hnot_val.
Qed.
 
End STLC.
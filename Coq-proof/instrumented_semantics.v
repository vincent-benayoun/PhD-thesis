Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.
Require Import operational_semantics.

Require Import over_instrumented_values.
Require Import oitval_instantiation.
Require Import oitval_val_conversion.
Require Import oitval_val_conversion_facts.

Require Import injection_operational_semantics.
Require Import ldna_in.
Require Import ldna_in_facts.
Require Import proof_injection_op_sem.

Require Import instrumented_values.
Require Import itval_val_conversion.


Definition is_filtered_itval (itu:itval) (p:pattern) : filtered_itval_result :=
  match itu, p with
    | IV _ (IV_ _ (IV_Constr0 n)), P_Constr0 n' =>
      if eq_nat_dec n n'
      then Filtered_itval_result_Match ITEnv_empty
      else Filtered_itval_result_Match_var
    | IV _ (IV_ _ (IV_Constr0 _)), _ => Filtered_itval_result_Match_var

    | IV _ (IV_ _ (IV_Constr1 n u)), P_Constr1 n' x =>
      if eq_nat_dec n n'
      then Filtered_itval_result_Match (ITEnv_cons x (IV nil u) ITEnv_empty)
      else Filtered_itval_result_Match_var
    | IV _ (IV_ _ (IV_Constr1 _ _)), _ => Filtered_itval_result_Match_var

    | IV _ (IV_ _ (IV_Couple u1 u2)), P_Couple x1 x2 =>
      Filtered_itval_result_Match (ITEnv_cons x1 (IV nil u1) (ITEnv_cons x2 (IV nil u2) ITEnv_empty))
    | IV _ (IV_ _ (IV_Couple _ _)), _ => Filtered_itval_result_Match_var

    | _,_ => Filtered_itval_result_Error
  end.



Inductive ival_of : itenv -> expr -> itval -> Prop :=
| IVal_of_Num :
  forall (v:Z) (c:itenv),
    ival_of c (Num v) (IV nil (IV_ nil (IV_Num v)))
| IVal_of_Ident :
  forall (c:itenv) (x:identifier) (uu:itval),
    assoc_ident_in_itenv x c = Ident_in_itenv uu
    -> ival_of c (Var x) uu
| IVal_of_Lambda :
  forall (c:itenv) (x:identifier) (e:expr) (uu:itval),
    uu = IV nil (IV_ nil (IV_Closure x e (itenv_to_ienv c)))
    -> ival_of c (Lambda x e) uu
| IVal_of_Rec :
  forall (c:itenv) (f x:identifier) (e:expr) (uu:itval),
    uu = IV nil (IV_ nil (IV_Rec_Closure f x e (itenv_to_ienv c)))
    -> ival_of c (Rec f x e) uu

| IVal_of_Apply :
  forall (c:itenv) (c1:ienv) (e1 e2 e : expr) (x : identifier)
    (uu2 uu:itval) (u2:ival) (d d1:ideps) (td1 td2 td:itdeps) (v:ival0),
(* construction de la valeur *)
    ival_of c e1 (IV td1 (IV_ d1 (IV_Closure x e c1)))
    -> ival_of c e2 uu2
    -> uu2 = IV td2 u2
    -> ival_of (ITEnv_cons x uu2 (ienv_to_itenv c1)) e (IV td (IV_ d v))
(* résultat de l'application *)
    -> uu = IV (conc_itdeps td1 (conc_itdeps td2 (conc_itdeps td d1))) (IV_ (conc_ideps d1 d) v)
    -> ival_of c (Apply e1 e2) uu

| IVal_of_Apply_Rec :
  forall (c:itenv) (c1:ienv) (e1 e2 e : expr) (f x:identifier)
    (uu1 uu2 uu:itval) (u2:ival) (d d1:ideps) (td1 td2 td:itdeps) (v:ival0),
(* construction de la valeur *)
    ival_of c e1 uu1
    -> uu1 = (IV td1 (IV_ d1 (IV_Rec_Closure f x e c1)))
    -> ival_of c e2 uu2
    -> ival_of (ITEnv_cons f uu1 (ITEnv_cons x uu2 (ienv_to_itenv c1))) e (IV td (IV_ d v))
    -> uu2 = IV td2 u2
(* résultat de l'application *)
    -> uu = IV (conc_itdeps td1 (conc_itdeps td2 (conc_itdeps td d1))) (IV_ (conc_ideps d1 d) v)
    -> ival_of c (Apply e1 e2) uu

| IVal_of_Let_in :
  forall (c:itenv) (x:identifier) (e1 e2:expr) (uu1 uu2:itval) (td1 td2:itdeps) (u1 u2:ival),
    ival_of c e1 uu1
    -> uu1 = (IV td1 u1)
    -> ival_of (ITEnv_cons x uu1 c) e2 uu2
    -> uu2 = (IV td2 u2)
    -> ival_of c (Let_in x e1 e2) (IV (conc_itdeps td1 td2) u2)

| IVal_of_If_true :
  forall (c:itenv) (e e1 e2:expr) (td td1:itdeps) (d d1:ideps) (uu1:itval) (v1:ival0),
    ival_of c e (IV td (IV_ d (IV_Bool true)))
    -> ival_of c e1 uu1
    -> uu1 = (IV td1 (IV_ d1 v1))
    -> ival_of c (If e e1 e2) (IV (conc_itdeps d (conc_itdeps td td1)) (IV_ (conc_ideps d d1) v1))

| IVal_of_If_false :
  forall (c:itenv) (e e1 e2:expr) (td td2:itdeps) (d d2:ideps) (uu2:itval) (v2:ival0),
    ival_of c e (IV td (IV_ d (IV_Bool false)))
    -> ival_of c e2 uu2
    -> uu2 = (IV td2 (IV_ d2 v2))
    -> ival_of c (If e e1 e2) (IV (conc_itdeps d (conc_itdeps td td2)) (IV_ (conc_ideps d d2) v2))

| IVal_of_Match : 
  forall (c c_p:itenv) (e e1 e2: expr) (p:pattern) (x:identifier) (uu uu1:itval) (td td1:itdeps) (d d1:ideps) (v v1:ival0),
    ival_of c e uu
    -> uu = (IV td (IV_ d v))
    -> is_filtered_itval uu p = Filtered_itval_result_Match c_p
    -> ival_of (conc_itenv c_p c) e1 uu1
    -> uu1 = (IV td1 (IV_ d1 v1))
    -> ival_of c (Expr_match e (p,e1) (Some (x,e2))) (IV (conc_itdeps d (conc_itdeps td td1)) (IV_ (conc_ideps d d1) v1))
(* TODO: il manque le cas de l'évaluation de (Expr_match e (p,e1) None), la match à une branche !!! *)

| IVal_of_Match_var : 
  forall (c:itenv) (e e1 e2: expr) (p:pattern) (x:identifier) (uu uu2:itval) (td td2:itdeps) (d d2:ideps) (v v2:ival0),
    ival_of c e uu
    -> uu = (IV td (IV_ d v))
    -> is_filtered_itval uu p = Filtered_itval_result_Match_var
    -> ival_of (ITEnv_cons x uu c) e2 uu2
    -> uu2 = (IV td2 (IV_ d2 v2))
    -> ival_of c (Expr_match e (p,e1) (Some (x,e2))) (IV (conc_itdeps d (conc_itdeps td td2)) (IV_ (conc_ideps d d2) v2))

| IVal_of_Constr0 :
  forall (c:itenv) (n:constr),
    ival_of c (Constr0 n) (IV nil (IV_ nil (IV_Constr0 n)))

| IVal_of_Constr1 :
  forall (c:itenv) (n:constr) (e:expr) (td:itdeps) (u:ival),
    ival_of c e (IV td u)
    -> ival_of c (Constr1 n e) (IV td (IV_ nil (IV_Constr1 n u)))
    
| IVal_of_Couple :
  forall (c:itenv) (e1 e2:expr) (td1 td2:itdeps) (u1 u2:ival),
    ival_of c e1 (IV td1 u1)
    -> ival_of c e2 (IV td2 u2)
    -> ival_of c (Couple e1 e2) (IV (conc_itdeps td1 td2) (IV_ nil (IV_Couple u1 u2)))

| IVal_of_Annot :
  forall (c:itenv) (l:label) (e:expr) (td:itdeps) (d:ideps) (v:ival0),
    ival_of c e (IV td (IV_ d v))
    -> ival_of c (Annot l e) (IV td (IV_ (cons l d) v))
.


Hint Constructors ival_of : ival_of.


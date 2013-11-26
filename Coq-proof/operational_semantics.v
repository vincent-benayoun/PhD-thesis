Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.

Definition is_filtered (v:val) (p:pattern) : filtered_result :=
match v, p with
| V_Constr0 n, P_Constr0 n' =>
  if eq_nat_dec n n'
  then Filtered_result_Match Env_empty
  else Filtered_result_Match_var
| V_Constr0 n, _ => Filtered_result_Match_var

| V_Constr1 n v, P_Constr1 n' x =>
  if eq_nat_dec n n'
  then Filtered_result_Match (Env_cons x v Env_empty)
  else Filtered_result_Match_var
| V_Constr1 _ _, _ => Filtered_result_Match_var

| V_Couple v1 v2, P_Couple x1 x2 =>
  Filtered_result_Match (Env_cons x1 v1 (Env_cons x2 v2 Env_empty))
| V_Couple _ _, _ => Filtered_result_Match_var

| _,_ => Filtered_result_Error
end.

(*
Inductive is_filtered : val -> pattern -> env -> Prop :=
| is_filtered_Constr0 :
  forall (n : constr),
  is_filtered (V_Constr0 n) (P_Constr0 n) (Env nil)
| is_filtered_Constr1 :
  forall (n : constr) (x : identifier) (v : val),
  is_filtered (V_Constr1 n v) (P_Constr1 n x) (Env (cons (x,v) nil))
| is_filtered_Couple :
  forall (x1 x2 : identifier) (v1 v2 : val),
  is_filtered (V_Couple v1 v2) (P_Couple x1 x2) (Env (cons (x1,v1) (cons (x2,v2) nil))).
*)

(*****************************************************************************)
(*                   We define now the Mini-ML dynamic semantics 
                     in the style of Natural Semantics  *)
(*****************************************************************************)

Inductive val_of : env -> expr -> val -> Prop :=
| Val_of_num :
  forall (v : Z) (c : env), val_of c (Num v) (V_Num v)
| Val_of_ident :
  forall (c : env) (i : identifier) (v : val),
    assoc_ident_in_env i c = Ident_in_env v
    -> val_of c (Var i) v
| Val_of_lambda :
  forall (c:env) (x:identifier) (e:expr),
    val_of c (Lambda x e) (V_Closure x e c)
| Val_of_rec :
  forall (c:env) (f x:identifier) (e:expr),
    val_of c (Rec f x e) (V_Rec_Closure f x e c)
| Val_of_apply :
  forall (c c1 : env) (e1 e2 e : expr) (x: identifier) (v2 v: val),
    val_of c e1 (V_Closure x e c1) ->
    val_of c e2 v2
    -> val_of (add_env x v2 c1) e v
    -> val_of c (Apply e1 e2) v
| Val_of_apply_rec :
  forall (c c1 : env) (e1 e2 e : expr) (f x: identifier) (v2 v: val),
    val_of c e1 (V_Rec_Closure f x e c1) ->
    val_of c e2 v2
    -> val_of (add_env  f (V_Rec_Closure f x e c1) (add_env x v2 c1)) e v
    -> val_of c (Apply e1 e2) v
| Val_of_let :
  forall (c : env) (x : identifier) (e1 e2 : expr) (v1 v : val),
    val_of c e1 v1
    -> val_of (add_env x v1 c) e2 v -> val_of c (Let_in x e1 e2) v

| Val_of_If_true :
  forall (c : env) (e e1 e2 : expr) (v : val),
    val_of c e (V_Bool true)
    -> val_of c e1 v
    -> val_of c (If e e1 e2) v

| Val_of_If_false :
  forall (c : env) (e e1 e2 : expr) (v : val),
    val_of c e (V_Bool false)
    -> val_of c e2 v
    -> val_of c (If e e1 e2) v

| Val_of_Match : 
  forall (c c_p : env) (e e1 : expr) (p : pattern) (v v_e : val) (br2 : option (identifier*expr)),
    val_of c e v_e
    -> is_filtered v_e p = Filtered_result_Match c_p
    -> val_of (conc_env c_p c) e1 v
    -> val_of c (Expr_match e (p,e1) br2) v
| Val_of_Match_var : 
  forall (c : env) (e e1 e2 : expr) (p : pattern) (v v_e : val) (x : identifier),
    val_of c e v_e
    -> is_filtered v_e p = Filtered_result_Match_var
    -> val_of (add_env x v_e c) e2 v
    -> val_of c (Expr_match e (p,e1) (Some (x,e2))) v

| Val_of_Constr0 : forall  c n,
  val_of c (Constr0 n) (V_Constr0 n) 
| Val_of_Constr1 : forall  c n e v,
  val_of c e v
  -> val_of c (Constr1 n e) (V_Constr1 n v) 

| Val_of_Couple : forall  c (e1 e2 : expr) (v1 v2 : val),
  val_of c e1 v1
  -> val_of c e2 v2
  -> val_of c (Couple e1 e2) (V_Couple v1 v2)

| Val_of_Annot : forall  c (l : label) (e : expr) v,
  val_of c e v
  -> val_of c (Annot l e) v
  .


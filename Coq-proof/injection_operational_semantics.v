Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.
Require Import operational_semantics.

Require Import over_instrumented_values.
Require Import oitval_instantiation.
Require Import oitval_val_conversion.


(*****************************************************************************)
(*                   We define now the Mini-ML dynamic semantics 
                     in the style of Natural Semantics  *)
(*****************************************************************************)

Inductive val_of_with_injection : label -> val -> oitenv -> expr -> val -> Prop :=
| Val_of_with_injection_Num :
  forall (l:label) (vl:val) (v:Z) (c:oitenv),
    val_of_with_injection l vl c (Num v) (V_Num v)
| Val_of_with_injection_Ident :
  forall (l:label) (vl v:val) (c:oitenv) (i:identifier) (uu:oitval),
    assoc_ident_in_oitenv i c = Ident_in_oitenv uu
    -> Some v = instantiate_oitval l vl uu
    -> val_of_with_injection l vl c (Var i) v
| Val_of_with_injection_Lambda :
  forall (l:label) (vl v:val) (c:oitenv) (c':env) (x:identifier) (e:expr),
    Some c' = instantiate_oitenv l vl c
    -> v = V_Closure x e c'
    -> val_of_with_injection l vl c (Lambda x e) v
| Val_of_with_injection_Rec :
  forall (l:label) (vl v:val) (c:oitenv) (c':env) (f x:identifier) (e:expr),
    Some c' = instantiate_oitenv l vl c
    -> v = V_Rec_Closure f x e c'
    -> val_of_with_injection l vl c (Rec f x e) v
| Val_of_with_injection_Apply :
  forall (l:label) (vl:val) (c:oitenv) (c1:env) (e1 e2 e:expr) (x:identifier) (v2 v:val),
    val_of_with_injection l vl c e1 (V_Closure x e c1)
    -> val_of_with_injection l vl c e2 v2
    -> val_of_with_injection l vl (OITEnv_cons x (val_to_oitval v2) (env_to_oitenv c1)) e v
    -> val_of_with_injection l vl c (Apply e1 e2) v
| Val_of_with_injection_Apply_rec :
  forall (l:label) (vl:val) (c : oitenv) (c1 : env) (e1 e2 e : expr) (f x : identifier) (v2 v : val),
    val_of_with_injection l vl c e1 (V_Rec_Closure f x e c1) ->
    val_of_with_injection l vl c e2 v2 ->
    val_of_with_injection l vl (env_to_oitenv (add_env  f (V_Rec_Closure f x e c1) (add_env x v2 c1))) e v ->
    val_of_with_injection l vl c (Apply e1 e2) v
| Val_of_with_injection_Let_in :
  forall (l:label) (vl:val) (c : oitenv) (i : identifier) (e1 e2 : expr) (v1 v2 : val),
    val_of_with_injection l vl c e1 v1
    -> val_of_with_injection l vl (OITEnv_cons i (val_to_oitval v1) c) e2 v2
    -> val_of_with_injection l vl c (Let_in i e1 e2) v2

| Val_of_with_injection_If_true :
  forall (l:label) (vl:val) (c : oitenv) (e e1 e2 : expr) (v : val),
    val_of_with_injection l vl c e (V_Bool true)
    -> val_of_with_injection l vl c e1 v
    -> val_of_with_injection l vl c (If e e1 e2) v

| Val_of_with_injection_If_false :
  forall (l:label) (vl:val) (c : oitenv) (e e1 e2 : expr) (v : val),
    val_of_with_injection l vl c e (V_Bool false)
    -> val_of_with_injection l vl c e2 v
    -> val_of_with_injection l vl c (If e e1 e2) v

| Val_of_with_injection_Match : 
  forall (l:label) (vl:val) (c:oitenv) (c_p:env) (e e1 : expr) (p : pattern) (v v_e : val) (br2 : option (identifier*expr)),
    val_of_with_injection l vl c e v_e
    -> is_filtered v_e p = Filtered_result_Match c_p
    -> val_of_with_injection l vl (conc_oitenv (env_to_oitenv c_p) c) e1 v
    -> val_of_with_injection l vl c (Expr_match e (p,e1) br2) v
| Val_of_with_injection_Match_var : 
  forall (l:label) (vl:val) (c : oitenv) (e e1 e2 : expr) (p : pattern) (v v_e : val) (x : identifier),
    val_of_with_injection l vl c e v_e
    -> is_filtered v_e p = Filtered_result_Match_var
    -> val_of_with_injection l vl (OITEnv_cons x (val_to_oitval v_e) c) e2 v
    -> val_of_with_injection l vl c (Expr_match e (p,e1) (Some (x,e2))) v

| Val_of_with_injection_Constr0 : forall (l:label) (vl:val)  c n,
  val_of_with_injection l vl c (Constr0 n) (V_Constr0 n) 
| Val_of_with_injection_Constr1 : forall (l:label) (vl:val)  c n e v,
  val_of_with_injection l vl c e v
  -> val_of_with_injection l vl c (Constr1 n e) (V_Constr1 n v) 

| Val_of_with_injection_Couple : forall (l:label) (vl:val)  c (e1 e2 : expr) (v1 v2 : val),
  val_of_with_injection l vl c e1 v1
  -> val_of_with_injection l vl c e2 v2
  -> val_of_with_injection l vl c (Couple e1 e2) (V_Couple v1 v2)

| Val_of_with_injection_Annot_eq : forall (l:label) (vl:val) c (e : expr),
  val_of_with_injection l vl c (Annot l e) vl

| Val_of_with_injection_Annot_neq : forall (l:label) (vl:val) c (l' : label) (e : expr) v,
  val_of_with_injection l vl c e v
  -> neq_label l l'
  -> val_of_with_injection l vl c (Annot l' e) v
  .


Hint Constructors val_of_with_injection : val_of_with_injection.


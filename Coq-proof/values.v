 Add Rec LoadPath "." as DEP_AI.

(*****************************************************************************)
(*     ML values and environments are defined with the following mutual       *)
(*     recursive definition                                                  *)
(*****************************************************************************)
Require Import language.
Require Import List.


Inductive val : Set :=
| V_Num     (n:Z)      : val
| V_Bool    (b:bool)   : val
| V_Constr0 (n:constr) : val
| V_Constr1 (n:constr) (v:val) : val
| V_Couple  (v1 v2:val) : val
| V_Closure (x:identifier) (e:expr) (c:env) : val
| V_Rec_Closure (f x:identifier) (e:expr) (c:env) : val
with env : Set :=
| Env_empty : env
| Env_cons (x:identifier) (v:val) (c':env) : env.

Inductive filtered_result : Set :=
| Filtered_result_Match (c_p:env)
| Filtered_result_Match_var
| Filtered_result_Error.


(*****************************************************************************)
(* Definition of assoc_ident_in_ctx which associates an identifier with 
its value *)
(*****************************************************************************)
Inductive ident_in_env : Set :=
  | Ident_not_in_env : ident_in_env
  | Ident_in_env (v:val) : ident_in_env.

Lemma ident_in_env_inv :
 forall i : ident_in_env,
 {v : val | i = Ident_in_env v} + {i = Ident_not_in_env}.
Proof.
simple induction i.
right; reflexivity.
intro v; left; exists v; auto.
Qed.


Fixpoint assoc_ident_in_env (x : identifier) (c : env) {struct c} :
 ident_in_env :=
match c with
| Env_empty => Ident_not_in_env
| Env_cons x' v c' =>
  if (beq_identifier x x')
  then (Ident_in_env v)
  else (assoc_ident_in_env x c')
end.

Definition add_env i u c := Env_cons i u c.

Fixpoint conc_env c c' :=
  match c with
    | Env_empty => c'
    | Env_cons x v c'' => Env_cons x v (conc_env c'' c')
  end.


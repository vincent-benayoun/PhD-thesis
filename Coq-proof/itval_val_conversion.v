Add Rec LoadPath "." as DEP_AI.

Require Import values.
Require Import instrumented_values.

(*----- SIMPLE TO INSTRUMENTED -----*)

Fixpoint val_to_ival (v:val) : ival :=
  IV_ nil
  match v with
    | V_Num n => IV_Num n
    | V_Bool b => IV_Bool b
    | V_Constr0 n => IV_Constr0 n
    | V_Constr1 n v => IV_Constr1 n (val_to_ival v)
    | V_Closure x e c => IV_Closure x e (env_to_ienv c)
    | V_Couple v1 v2 => IV_Couple (val_to_ival v1) (val_to_ival v2)
    | V_Rec_Closure f x e c => IV_Rec_Closure f x e (env_to_ienv c)
  end
  
with env_to_ienv (c:env) : ienv :=
  match c with
    | Env_empty => IEnv_empty
    | Env_cons x v c' => IEnv_cons x (val_to_ival v) (env_to_ienv c')
  end.

Definition val_to_itval (v:val) : itval := IV nil (val_to_ival v).

Fixpoint env_to_itenv (c:env) : itenv :=
  match c with
    | Env_empty => ITEnv_empty
    | Env_cons x v c' => ITEnv_cons x (val_to_itval v) (env_to_itenv c')
  end.


(*----- INSTRUMENTED TO SIMPLE -----*)

Fixpoint ival_to_val (u:ival) :=
  match u with
    | IV_ d v => ival0_to_val v
  end

with ival0_to_val (v:ival0) :=
  match v with
    | IV_Num n => V_Num n
    | IV_Bool b => V_Bool b
    | IV_Constr0 n => V_Constr0 n
    | IV_Constr1 n u => V_Constr1 n (ival_to_val u)
    | IV_Closure x e c => V_Closure x e (ienv_to_env c)
    | IV_Couple u1 u2 => V_Couple (ival_to_val u1) (ival_to_val u2)
    | IV_Rec_Closure f x e c => V_Rec_Closure f x e (ienv_to_env c)
  end 

with ienv_to_env (c:ienv) :=
  match c with
    | IEnv_empty => Env_empty
    | IEnv_cons x u c' => Env_cons x (ival_to_val u) (ienv_to_env c')
  end.

Definition itval_to_val (uu:itval) :=
  match uu with
    | IV td u => ival_to_val u
  end.

Fixpoint itenv_to_env (c:itenv) :=
  match c with
    | ITEnv_empty => Env_empty
    | ITEnv_cons x uu c' => Env_cons x (itval_to_val uu) (itenv_to_env c')
  end.


(*----- BETWEEN OVER-INSTRUMENTED WITH AND WITHOUT TERMINATION -----*)


Definition ival_to_itval (u:ival) := IV nil u.

Fixpoint ienv_to_itenv (c:ienv) :=
  match c with
    | IEnv_empty => ITEnv_empty
    | IEnv_cons x u c' => ITEnv_cons x (ival_to_itval u) (ienv_to_itenv c')
  end.


Definition itval_to_ival (uu:itval) :=
  match uu with
    | IV td u => u
  end.
      
Fixpoint itenv_to_ienv (c:itenv) :=
  match c with
    | ITEnv_empty => IEnv_empty
    | ITEnv_cons x uu c' => IEnv_cons x (itval_to_ival uu) (itenv_to_ienv c')
  end.


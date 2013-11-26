
Require Import values.
Require Import over_instrumented_values.

(*----- SIMPLE TO OVER-INSTRUMENTED -----*)

Fixpoint val_to_oival (v:val) : oival :=
  OIV_ nil
  match v with
    | V_Num n => OIV_Num n
    | V_Bool b => OIV_Bool b
    | V_Constr0 n => OIV_Constr0 n
    | V_Constr1 n v => OIV_Constr1 n (val_to_oival v)
    | V_Closure x e c => OIV_Closure x e (env_to_oienv c)
    | V_Couple v1 v2 => OIV_Couple (val_to_oival v1) (val_to_oival v2)
    | V_Rec_Closure f x e c => OIV_Rec_Closure f x e (env_to_oienv c)
  end
  
with env_to_oienv (c:env) : oienv :=
  match c with
    | Env_empty => OIEnv_empty
    | Env_cons x v c' => OIEnv_cons x (val_to_oival v) (env_to_oienv c')
  end.

Definition val_to_oitval (v:val) : oitval := OIV nil (val_to_oival v).

Fixpoint env_to_oitenv (c:env) : oitenv :=
  match c with
    | Env_empty => OITEnv_empty
    | Env_cons x v c' => OITEnv_cons x (val_to_oitval v) (env_to_oitenv c')
  end.


(*----- OVER-INSTRUMENTED TO SIMPLE -----*)

Fixpoint oival_to_val (u:oival) :=
  match u with
    | OIV_ d v => oival0_to_val v
  end

with oival0_to_val (v:oival0) :=
  match v with
    | OIV_Num n => V_Num n
    | OIV_Bool b => V_Bool b
    | OIV_Constr0 n => V_Constr0 n
    | OIV_Constr1 n u => V_Constr1 n (oival_to_val u)
    | OIV_Closure x e c => V_Closure x e (oienv_to_env c)
    | OIV_Couple u1 u2 => V_Couple (oival_to_val u1) (oival_to_val u2)
    | OIV_Rec_Closure f x e c => V_Rec_Closure f x e (oienv_to_env c)
  end 

with oienv_to_env (c:oienv) :=
  match c with
    | OIEnv_empty => Env_empty
    | OIEnv_cons x u c' => Env_cons x (oival_to_val u) (oienv_to_env c')
  end.

Definition oitval_to_val (uu:oitval) :=
  match uu with
    | OIV td u => oival_to_val u
  end.

Fixpoint oitenv_to_env (c:oitenv) :=
  match c with
    | OITEnv_empty => Env_empty
    | OITEnv_cons x uu c' => Env_cons x (oitval_to_val uu) (oitenv_to_env c')
  end.


(*----- BETWEEN OVER-INSTRUMENTED WITH AND WITHOUT TERMINATION -----*)


Definition oival_to_oitval (u:oival) := OIV nil u.

Fixpoint oienv_to_oitenv (c:oienv) :=
  match c with
    | OIEnv_empty => OITEnv_empty
    | OIEnv_cons x u c' => OITEnv_cons x (oival_to_oitval u) (oienv_to_oitenv c')
  end.


Definition oitval_to_oival (uu:oitval) :=
  match uu with
    | OIV td u => u
  end.
      
Fixpoint oitenv_to_oienv (c:oitenv) :=
  match c with
    | OITEnv_empty => OIEnv_empty
    | OITEnv_cons x uu c' => OIEnv_cons x (oitval_to_oival uu) (oitenv_to_oienv c')
  end.


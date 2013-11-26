Add Rec LoadPath "." as DEP_AI.


Require Import values.
Require Import over_instrumented_values.
Require Import instrumented_values.


(* CONVERSION OF INSTRUMENTED VALUES TO OVER-INSTRUMENTED VALUES *)

(* TODO: remplacer V_Num 0 par None (cf. over_instrumented_semantics) *)
Fixpoint ideps_to_oideps (id:ideps) : oideps :=
  match id with
    | nil => nil
    | cons l id' => cons (l, fun v => V_Num 0) (ideps_to_oideps id')
  end.

Fixpoint itdeps_to_oitdeps (itd:itdeps) : oitdeps :=
  match itd with
    | nil => nil
    | cons l itd' => cons (l, fun v => true) (itdeps_to_oitdeps itd')
  end.

Fixpoint ival_to_oival (iu:ival) : oival :=
  match iu with
    | IV_ d v => OIV_ (ideps_to_oideps d) (ival0_to_oival0 v)
  end
    
with ival0_to_oival0 (iv:ival0) : oival0 :=
       match iv with
         | IV_Num n => OIV_Num n
         | IV_Bool b => OIV_Bool b
         | IV_Constr0 n => OIV_Constr0 n
         | IV_Constr1 n u => OIV_Constr1 n (ival_to_oival u)
         | IV_Closure x e c => OIV_Closure x e (ienv_to_oienv c)
         | IV_Couple u1 u2 => OIV_Couple (ival_to_oival u1) (ival_to_oival u2)
         | IV_Rec_Closure f x e c => OIV_Rec_Closure f x e (ienv_to_oienv c)
       end

with ienv_to_oienv (ic:ienv) : oienv :=
       match ic with
         | IEnv_empty => OIEnv_empty
         | IEnv_cons x iu ic' => OIEnv_cons x (ival_to_oival iu) (ienv_to_oienv ic')
       end.

Fixpoint itval_to_oitval (itu:itval) : oitval :=
  match itu with
    | IV td u => OIV (itdeps_to_oitdeps td) (ival_to_oival u)
  end.

         
Fixpoint itenv_to_oitenv (itc:itenv) : oitenv :=
       match itc with
         | ITEnv_empty => OITEnv_empty
         | ITEnv_cons x uu c' => OITEnv_cons x (itval_to_oitval uu) (itenv_to_oitenv c')
       end.


(* CONVERSION OF OIVER-INSTRUMENTED VALUES TO INSTRUMENTED VALUES *)

Fixpoint oitdeps_to_itdeps (oitd:oitdeps) : itdeps :=
  match oitd with
    | nil => nil
    | cons (l,f) oitd' => cons l (oitdeps_to_itdeps oitd')
  end.

Fixpoint oideps_to_ideps (oid:oideps) : ideps :=
  match oid with
    | nil => nil
    | cons (l,tf) oid' => cons l (oideps_to_ideps oid')
  end.

Fixpoint oival_to_ival (oiu:oival) : ival :=
  match oiu with
    | OIV_ oid oiv => IV_ (oideps_to_ideps oid) (oival0_to_ival0 oiv)
  end

with oival0_to_ival0 (oiv:oival0) : ival0 :=
       match oiv with
         | OIV_Num n => IV_Num n
         | OIV_Bool b => IV_Bool b
         | OIV_Constr0 n => IV_Constr0 n
         | OIV_Constr1 n oiu => IV_Constr1 n (oival_to_ival oiu)
         | OIV_Closure x e oic => IV_Closure x e (oienv_to_ienv oic)
         | OIV_Couple u1 u2 => IV_Couple (oival_to_ival u1) (oival_to_ival u2)
         | OIV_Rec_Closure f x e oic => IV_Rec_Closure f x e (oienv_to_ienv oic)
       end

with oienv_to_ienv (oic:oienv) : ienv :=
       match oic with
         | OIEnv_empty => IEnv_empty
         | OIEnv_cons x oiu oic' => IEnv_cons x (oival_to_ival oiu) (oienv_to_ienv oic')
       end
.      

Fixpoint oitval_to_itval (oitu:oitval) : itval :=
  match oitu with
    | OIV td u => IV (oitdeps_to_itdeps td) (oival_to_ival u)
  end.

Fixpoint oitenv_to_itenv (oitc:oitenv) : itenv :=
  match oitc with
    | OITEnv_empty => ITEnv_empty
    | OITEnv_cons x uu oitc' => ITEnv_cons x (oitval_to_itval uu) (oitenv_to_itenv oitc')
  end.
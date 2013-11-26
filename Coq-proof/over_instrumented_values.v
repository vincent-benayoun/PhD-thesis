(*****************************************************************************)
(*     ML values and environments are defined with the following mutual       *)
(*     recursive definition                                                  *)
(*****************************************************************************)
Add Rec LoadPath "." as DEP_AI.


Require Import language.
Require Import values.
Require Import List.

Definition oitdeps : Set := list (label * (val -> bool)).
Definition oideps : Set := list (label * (val -> val)).

Inductive oival : Set :=
| OIV_ (d:oideps) (v:oival0) : oival
with oival0 : Set :=
| OIV_Num     (n:Z)      : oival0
| OIV_Bool    (b:bool)   : oival0
| OIV_Constr0 (n:constr) :  oival0
| OIV_Constr1 (n:constr) (u:oival) : oival0
| OIV_Closure (x:identifier) (e:expr) (c:oienv) : oival0
| OIV_Couple  (u1 u2:oival) : oival0
| OIV_Rec_Closure (f x:identifier) (e:expr) (c:oienv) : oival0
with oienv : Set :=
| OIEnv_empty : oienv
| OIEnv_cons (x:identifier) (u:oival) (c':oienv) : oienv.

Inductive oitval : Set :=
| OIV (td:oitdeps) (u:oival) : oitval
with oitenv : Set :=
| OITEnv_empty : oitenv
| OITEnv_cons (x:identifier) (uu:oitval) (c':oitenv) : oitenv.


Inductive filtered_oitval_result : Set :=
| Filtered_oitval_result_Match (c_p:oitenv)
| Filtered_oitval_result_Match_var
| Filtered_oitval_result_Error.


(* Concatenation of environments *)

Fixpoint conc_oideps (d d':oideps) :=
  match d with
    | nil => d'
    | cons x tl => cons x (conc_oideps tl d')
  end.

Fixpoint conc_oitdeps (td td':oitdeps) :=
  match td with
    | nil => td'
    | cons x tl => cons x (conc_oitdeps tl td')
  end.


(*****************************************************************************)
(* Definition of assoc_ident_in_ctx which associates an identifier with 
its value *)
(*****************************************************************************)
Inductive ident_in_oitenv : Set :=
  | Ident_not_in_oitenv : ident_in_oitenv
  | Ident_in_oitenv : oitval -> ident_in_oitenv.

Lemma ident_in_oitenv_inv :
 forall i : ident_in_oitenv,
 {uu : oitval | i = Ident_in_oitenv uu} + {i = Ident_not_in_oitenv}.
Proof.
simple induction i.
right; auto.
intro uu; left; exists uu; auto.
Qed.


Fixpoint assoc_ident_in_oitenv (x : identifier) (c : oitenv) {struct c} :
 ident_in_oitenv :=
match c with
| OITEnv_empty => Ident_not_in_oitenv
| OITEnv_cons x' u c' =>
  if (beq_identifier x x')
  then (Ident_in_oitenv u)
  else (assoc_ident_in_oitenv x c')
end.

Fixpoint conc_oitenv c c' :=
  match c with
    | OITEnv_empty => c'
    | OITEnv_cons x v c'' => OITEnv_cons x v (conc_oitenv c'' c')
  end.

(****)

Definition option_map2 {A B C:Type} (f:A->B->C) o1 o2 :=
  match o1 with
    | Some a =>
      match o2 with
        | Some b => Some (f a b)
        | None => None
      end
    | None => None
  end.


Scheme val_ind2 := Induction for val Sort Prop
with env_ind2 := Induction for env Sort Prop.

Scheme oival_ind2 := Induction for oival Sort Prop
with oival0_ind2 := Induction for oival0 Sort Prop
with oienv_ind2 := Induction for oienv Sort Prop.

Scheme oitval_ind2 := Induction for oitval Sort Prop
with oitenv_ind2 := Induction for oitenv Sort Prop.

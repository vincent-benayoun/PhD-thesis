(*****************************************************************************)
(*     ML values and environments are defined with the following mutual       *)
(*     recursive definition                                                  *)
(*****************************************************************************)
Add Rec LoadPath "." as DEP_AI.


Require Import language.
Require Import values.
Require Import List.

Definition itdeps : Set := list (label).
Definition ideps : Set := list (label).

Inductive ival : Set :=
| IV_ (d:ideps) (v:ival0) : ival
with ival0 : Set :=
| IV_Num     (n:Z)      : ival0
| IV_Bool    (b:bool)   : ival0
| IV_Constr0 (n:constr) : ival0
| IV_Constr1 (n:constr) (u:ival) : ival0
| IV_Closure (x:identifier) (e:expr) (c:ienv) : ival0
| IV_Couple  (u1 u2:ival) : ival0
| IV_Rec_Closure (f x:identifier) (e:expr) (c:ienv) : ival0
with ienv : Set :=
| IEnv_empty : ienv
| IEnv_cons (x:identifier) (u:ival) (c':ienv) : ienv.

Inductive itval : Set :=
| IV (td:itdeps) (u:ival) : itval
with itenv : Set :=
| ITEnv_empty : itenv
| ITEnv_cons (x:identifier) (uu:itval) (c':itenv) : itenv.


Inductive filtered_itval_result : Set :=
| Filtered_itval_result_Match (c_p:itenv)
| Filtered_itval_result_Match_var
| Filtered_itval_result_Error.


(* Concatenation of environments *)

Fixpoint conc_ideps (d d':ideps) :=
  match d with
    | nil => d'
    | cons x tl => cons x (conc_ideps tl d')
  end.

Fixpoint conc_itdeps (td td':itdeps) :=
  match td with
    | nil => td'
    | cons x tl => cons x (conc_itdeps tl td')
  end.


(*****************************************************************************)
(* Definition of assoc_ident_in_ctx which associates an identifier with 
its value *)
(*****************************************************************************)
Inductive ident_in_itenv : Set :=
  | Ident_not_in_itenv : ident_in_itenv
  | Ident_in_itenv : itval -> ident_in_itenv.

Lemma ident_in_itenv_inv :
 forall i : ident_in_itenv,
 {uu : itval | i = Ident_in_itenv uu} + {i = Ident_not_in_itenv}.
Proof.
simple induction i.
right; auto.
intro uu; left; exists uu; auto.
Qed.


Fixpoint assoc_ident_in_itenv (x:identifier) (c:itenv) {struct c} :
 ident_in_itenv :=
match c with
| ITEnv_empty => Ident_not_in_itenv
| ITEnv_cons x' u c' =>
  if (beq_identifier x x')
  then (Ident_in_itenv u)
  else (assoc_ident_in_itenv x c')
end.

Fixpoint conc_itenv c c' :=
  match c with
    | ITEnv_empty => c'
    | ITEnv_cons x v c'' => ITEnv_cons x v (conc_itenv c'' c')
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

Scheme ival_ind2 := Induction for ival Sort Prop
with ival0_ind2 := Induction for ival0 Sort Prop
with ienv_ind2 := Induction for ienv Sort Prop.

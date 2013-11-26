Add Rec LoadPath "." as DEP_AI.


Require Import language.
Require Import values.
Require Import List.


Definition atdeps : Set := list (label).
Definition adeps : Set := list (label).

Inductive aval : Set :=
| AV (d:adeps) (v:aval0) : aval
with aval0 : Set :=
| AV_Bottom             : aval0
| AV_Top                : aval0
| AV_Constr0 (n:constr) : aval0
| AV_Constr1 (n:constr) (au:aval) : aval0
| AV_Couple  (au1 au2:aval) : aval0
| AV_Closure (x:identifier) (e:expr) (ac:aenv) : aval0
| AV_Rec_Closure (f x:identifier) (e:expr) (ac:aenv) : aval0
with aenv : Set :=
| AEnv_empty : aenv
| AEnv_cons (x:identifier) (au:aval) (ac':aenv) : aenv.

Inductive atval : Set :=
| ATV (atd:atdeps) (au:aval) : atval
with atenv : Set :=
| ATEnv_empty : atenv
| ATEnv_cons (x:identifier) (atu:atval) (ac':atenv) : atenv.


(* Result of pattern matching *)

Inductive filtered_atval_result : Set :=
| Filtered_atval_result_Match (atc_p:atenv)
| Filtered_atval_result_Match_var
| Filtered_atval_result_Match_unknown (atc_p:atenv)
| Filtered_atval_result_Error.


(* Searching identifier in atenv *)

Inductive ident_in_atenv : Set :=
| Ident_not_in_atenv : ident_in_atenv
| Ident_in_atenv : atval -> ident_in_atenv.

Lemma ident_in_atenv_inv :
 forall i : ident_in_atenv,
 {atu : atval | i = Ident_in_atenv atu} + {i = Ident_not_in_atenv}.
Proof.
  simple induction i.
  right; auto.
  intro atu; left; exists atu; auto.
Qed.


Fixpoint assoc_ident_in_atenv (x:identifier) (atc:atenv) {struct atc} : ident_in_atenv :=
  match atc with
    | ATEnv_empty => Ident_not_in_atenv
    | ATEnv_cons x' atu atc' =>
      if (beq_identifier x x')
      then (Ident_in_atenv atu)
      else (assoc_ident_in_atenv x atc')
  end.

(* Concatenation of dependencies *)

Fixpoint conc_adeps (d d':adeps) :=
  match d with
    | nil => d'
    | cons x tl => cons x (conc_adeps tl d')
  end.

Fixpoint conc_atdeps (td td':atdeps) :=
  match td with
    | nil => td'
    | cons x tl => cons x (conc_atdeps tl td')
  end.

(* Concatenation of environments *)

Fixpoint conc_atenv c c' :=
  match c with
    | ATEnv_empty => c'
    | ATEnv_cons x v c'' => ATEnv_cons x v (conc_atenv c'' c')
  end.


(* conversions between atval and aval *)


Definition aval_to_atval (au:aval) := ATV nil au.

Fixpoint aenv_to_atenv (ac:aenv) :=
  match ac with
    | AEnv_empty => ATEnv_empty
    | AEnv_cons x au ac' => ATEnv_cons x (aval_to_atval au) (aenv_to_atenv ac')
  end.

Definition atval_to_aval (atu:atval) :=
  match atu with
    | ATV atd au => au
  end.
      
Fixpoint atenv_to_aenv (atc:atenv) :=
  match atc with
    | ATEnv_empty => AEnv_empty
    | ATEnv_cons x atu atc' => AEnv_cons x (atval_to_aval atu) (atenv_to_aenv atc')
  end.




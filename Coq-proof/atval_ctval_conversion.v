Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.

Require Import instrumented_values.
Require Import collecting_values.
Require Import abstract_values.

Require Import ensembles.


Fixpoint aval0_to_ival0s (av:aval0) : Ensemble ival0 :=
  match av with
    | AV_Bottom => (fun iv => False)
    | AV_Top => (fun iv => True)
    | AV_Constr0 n => Singleton _ (IV_Constr0 n)
    | AV_Constr1 n (AV ad av) =>
      let ivs := aval0_to_ival0s av in
      SetMap (fun iv => IV_Constr1 n (IV_ ad iv)) ivs
    | AV_Couple (AV ad1 av1) (AV ad2 av2) =>
      let ivs1 := aval0_to_ival0s av1 in
      let ivs2 := aval0_to_ival0s av2 in
      SetMap2 (fun iv1 iv2 => IV_Couple (IV_ ad1 iv1) (IV_ ad2 iv2)) ivs1 ivs2
    | AV_Closure x e ac =>
      let ics := aenv_to_cenv ac in
      SetMap (fun ic => IV_Closure x e ic) ics
    | AV_Rec_Closure f x e ac =>
      let ics := aenv_to_cenv ac in
      SetMap (fun ic => IV_Rec_Closure f x e ic) ics
  end

with aenv_to_cenv (ac:aenv) : Ensemble ienv :=
       match ac with
         | AEnv_empty =>
           Singleton _ (IEnv_empty)
         | AEnv_cons x (AV ad av) ac' =>
           let ivs := aval0_to_ival0s av in
           let ics := aenv_to_cenv ac' in
           SetMap2 (fun iv ic => IEnv_cons x (IV_ ad iv) ic) ivs ics
       end
.

Definition atval_to_ctval (atu:atval) : ctval :=
  match atu with
    | ATV atd (AV ad av) => 
      CTVal atd ad (aval0_to_ival0s av)
  end.

Fixpoint atenv_to_ctenv (atc:atenv) : ctenv :=
       match atc with
         | ATEnv_empty => CTEnv_empty
         | ATEnv_cons x atu atc' =>
           CTEnv_cons x (atval_to_ctval atu) (atenv_to_ctenv atc')
       end.

Inductive d_of_ivals : Ensemble ival -> ideps -> Prop :=
| D_of_imval :
    forall (ius:Ensemble ival) (d:ideps),
      (forall (l:label),
         (exists (id:ideps) (iv:ival0), List.In l id /\ In _ ius (IV_ id iv))
         <->
         List.In l d
      )
      -> d_of_ivals ius d.


Inductive ivals_to_aval : Ensemble ival -> aval -> Prop :=
| Ivals_to_aval_Constr0 :
    forall (ius:Ensemble ival) (n:constr) (ad:adeps),
    Included _ ius (fun iu =>
                      match iu with
                        | IV_ _ (IV_Constr0 n') =>  n = n'
                        | _ => False
                      end)
    -> Inhabited _ ius
    -> d_of_ivals ius ad
    -> ivals_to_aval ius (AV ad (AV_Constr0 n))
| Ivals_to_aval_Constr1 :
    forall (ius:Ensemble ival) (n:constr) (ad:adeps) (au:aval),
    Included _ ius (fun iu =>
                      match iu with
                        | IV_ _ (IV_Constr1 n' _) =>  n = n'
                        | _ => False
                      end)
    -> Inhabited _ ius
    -> d_of_ivals ius ad
    -> ivals_to_aval (SetMap (fun iu =>
                                match iu with
                                  | IV_ _ (IV_Constr1 n' iu') =>  iu'
                                  | _ => IV_ nil (IV_Num 0)
                                end) ius) au
    -> ivals_to_aval ius (AV ad (AV_Constr1 n au)).

Inductive ctval_to_atval : ctval -> atval -> Prop :=
| Ctval_to_atval :
    forall (td:itdeps) (d:ideps) (ivs:Ensemble ival0) (au:aval),
      ivals_to_aval (SetMap (fun iv => IV_ d iv) ivs) au
      -> ctval_to_atval (CTVal td d ivs) (ATV td au)
.


Inductive ctenv_to_atenv : ctenv -> atenv -> Prop :=
| Ctenv_to_atenv_empty :
    ctenv_to_atenv CTEnv_empty ATEnv_empty
| Ctenv_to_atenv_cons :
    forall (ctv:ctval) (ctc:ctenv)
           (atu:atval) (atc:atenv)
           (x:identifier),
    ctval_to_atval ctv atu
    -> ctenv_to_atenv ctc atc
    -> ctenv_to_atenv (CTEnv_cons x ctv ctc) (ATEnv_cons x atu atc)
.

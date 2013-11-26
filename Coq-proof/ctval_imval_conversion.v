
Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.
Require Import operational_semantics.

Require Import instrumented_values.
Require Import instrumented_semantics.

Require Import itval_val_conversion.

Require Import instrumented_multiple_values.

Require Import collecting_values.

Require Import ensembles.


(* CTVAL TO IMVAL *)

Fixpoint ctval_to_imval (ctv:ctval) : imval :=
  match ctv with
    | CTVal td d ivs =>
      SetMap (fun iv => IV td (IV_ d iv)) ivs
  end.

Fixpoint append_ctenv_to_imenv (ctc:ctenv) (imc:imenv) : Ensemble itenv :=
  match ctc with
    | CTEnv_empty => imc
    | CTEnv_cons x ctv ctc' =>
      match ctv with
        | CTVal td d ivs =>
          SetMap2 (fun iv itc => ITEnv_cons x (IV td (IV_ d iv)) itc)
                  ivs
                  (append_ctenv_to_imenv ctc' imc)
      end
  end.

Definition ctenv_to_imenv (ctc:ctenv) : Ensemble itenv :=
  append_ctenv_to_imenv ctc (Singleton _ (ITEnv_empty)).


(* IMVAL TO CTVAL *)

Inductive td_of_imval : imval -> itdeps -> Prop :=
| Td_of_imval :
    forall (imv:imval) (td:itdeps),
      (forall (l:label),
         (exists (itd:itdeps) (id:ideps) (iv:ival0), List.In l itd /\ In _ imv (IV itd (IV_ id iv)))
         <->
         List.In l td
      )
      -> td_of_imval imv td.

Inductive d_of_imval : imval -> itdeps -> Prop :=
| D_of_imval :
    forall (imv:imval) (d:itdeps),
      (forall (l:label),
         (exists (itd:itdeps) (id:ideps) (iv:ival0), List.In l id /\ In _ imv (IV itd (IV_ id iv)))
         <->
         List.In l d
      )
      -> d_of_imval imv d.

Inductive imval_to_ctval : imval -> ctval -> Prop :=
| Imval_to_ctval :
    forall (imv:imval) (td:itdeps) (d:ideps) (ivs:Ensemble ival0),
      td_of_imval imv td
      -> d_of_imval imv d
      -> ivs = SetMap (fun itv => match itv with
                                    | IV _ (IV_ _ v) => v
                                  end) imv
      -> imval_to_ctval imv (CTVal td d ivs).


Inductive imenv_to_ctenv : imenv -> ctenv -> Prop :=
| Imenv_to_ctenv_empty :
    forall (imc:imenv),
      imc = Singleton _ ITEnv_empty
      -> imenv_to_ctenv imc CTEnv_empty
| Imenv_to_ctenv_cons :
    forall (imc imc':imenv)
           (x:identifier) (ctv:ctval) (imv:imval) (td:itdeps) (d:ideps) (ivs:Ensemble ival0) (ctc':ctenv),
      (* imc is the set of {(x,itu); itc'} for itu in a given imv and itc in a given imc' *)
      Same_set _ imc (SetMap2 (fun itu itc => ITEnv_cons x itu itc) imv imc')
      (* ctv is the union of all itu in imv *)
      -> ctv = CTVal td d ivs
      -> td_of_imval imv td
      -> d_of_imval imv d
      -> Same_set _ ivs (SetMap (fun itu => match itu with IV _ (IV_ _ iv) => iv end) imv)
      (* ctc' is the abstraction of imc' *)
      -> imenv_to_ctenv imc' ctc'
      -> imenv_to_ctenv imc (CTEnv_cons x ctv ctc').
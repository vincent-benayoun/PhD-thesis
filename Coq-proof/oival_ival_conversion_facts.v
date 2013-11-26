
Add Rec LoadPath "." as DEP_AI.


Require Import over_instrumented_values.
Require Import instrumented_values.
Require Import oival_ival_conversion.

Require Import itval_val_conversion.
Require Import oitval_val_conversion.


(* COMPOSITION *)


Lemma itdeps_to_oitdeps_to_itdeps :
  forall (itd:itdeps),
    oitdeps_to_itdeps (itdeps_to_oitdeps itd) = itd.
Proof.
  intros itd.
  induction itd.
  auto.
  simpl.
  f_equal; assumption.
Qed.

Lemma ideps_to_oideps_to_ideps :
  forall (id:ideps),
    oideps_to_ideps (ideps_to_oideps id) = id.
Proof.
  intros id.
  induction id.
  auto.
  simpl.
  f_equal; assumption.
Qed.

Lemma ival0_to_oival0_to_ival0 :
  forall (iv:ival0),
    oival0_to_ival0 (ival0_to_oival0 iv) = iv.
Proof.
  apply (ival0_ind2
           (fun iu => oival_to_ival (ival_to_oival iu) = iu)
           (fun iv => oival0_to_ival0 (ival0_to_oival0 iv) = iv)
           (fun ic => oienv_to_ienv (ienv_to_oienv ic) = ic)
        );
  simpl; auto; intros; f_equal; auto; try (apply ideps_to_oideps_to_ideps).
Qed.

Lemma ival_to_oival_to_ival :
  forall (iu:ival),
    oival_to_ival (ival_to_oival iu) = iu.
Proof.
  apply (ival_ind2
           (fun iu => oival_to_ival (ival_to_oival iu) = iu)
           (fun iv => oival0_to_ival0 (ival0_to_oival0 iv) = iv)
           (fun ic => oienv_to_ienv (ienv_to_oienv ic) = ic)
        );
  simpl; auto; intros; f_equal; auto; try (apply ideps_to_oideps_to_ideps).
Qed.

Lemma ienv_to_oienv_to_ienv :
  forall (ic:ienv),
    oienv_to_ienv (ienv_to_oienv ic) = ic.
Proof.
  apply (ienv_ind2
           (fun iu => oival_to_ival (ival_to_oival iu) = iu)
           (fun iv => oival0_to_ival0 (ival0_to_oival0 iv) = iv)
           (fun ic => oienv_to_ienv (ienv_to_oienv ic) = ic)
        );
  simpl; auto; intros; f_equal; auto; try (apply ideps_to_oideps_to_ideps).
Qed.

Lemma itval_to_oitval_to_itval :
  forall (itu:itval),
    oitval_to_itval (itval_to_oitval itu) = itu.
Proof.
  intros itu.
  induction itu.
  simpl.
  f_equal.
  apply itdeps_to_oitdeps_to_itdeps.
  apply ival_to_oival_to_ival.
Qed.

Lemma itenv_to_oitenv_to_itenv :
  forall (itc:itenv),
    oitenv_to_itenv (itenv_to_oitenv itc) = itc.
Proof.

  induction itc; auto.

  simpl.
  f_equal; auto.
  apply itval_to_oitval_to_itval.
Qed.

Lemma itval_to_oival_via_ival_or_via_itval :
  forall (itu:itval),
    ival_to_oival (itval_to_ival itu) = oitval_to_oival (itval_to_oitval itu).
Proof.
  intros itu.  
  induction itu.
  simpl.
  reflexivity.
Qed.

Lemma itenv_to_oienv_via_ienv_or_via_oitenv :
  forall (itc:itenv),
    ienv_to_oienv (itenv_to_ienv itc) = oitenv_to_oienv (itenv_to_oitenv itc).
Proof.
  intros itc.
  induction itc.
  auto.
  simpl.
  f_equal; auto.
  apply itval_to_oival_via_ival_or_via_itval.
Qed.

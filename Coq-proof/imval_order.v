
Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.

Require Import instrumented_values.
Require Import instrumented_multiple_values.

Require Import itval_val_conversion.

Require Import List.
Require Import ensembles.


Definition list_Included {A:Set} (l1 l2:list A) :=
  forall (x:A),
    List.In x l1 -> List.In x l2.


Inductive le_itval : itval -> itval -> Prop :=
| Le_itval :
    forall (td1 td2:itdeps) (iu1 iu2:ival),
      list_Included td1 td2
      -> le_ival iu1 iu2
      -> le_itval (IV td1 iu1) (IV td2 iu2)

with le_ival : ival -> ival -> Prop :=
| Le_ival :
    forall (d1 d2:ideps) (iv1 iv2:ival0),
      list_Included d1 d2
      -> le_ival0 iv1 iv2
      -> le_ival (IV_ d1 iv1) (IV_ d2 iv2)

with le_ival0 : ival0 -> ival0 -> Prop :=
| Le_ival0_Num :
    forall (n:Z),
      le_ival0 (IV_Num n) (IV_Num n)
| Le_ival0_Bool :
    forall (b:bool),
      le_ival0 (IV_Bool b) (IV_Bool b)
| Le_ival0_Constr0 :
    forall (n:constr),
      le_ival0 (IV_Constr0 n) (IV_Constr0 n)
| Le_ival0_Constr1 :
    forall (n:constr) (itu itu':ival),
      le_ival itu itu'
      -> le_ival0 (IV_Constr1 n itu) (IV_Constr1 n itu')
| Le_ival0_Couple :
    forall (itu1 itu2 itu1' itu2':ival),
      le_ival itu1 itu1'
      -> le_ival itu2 itu2'
      -> le_ival0 (IV_Couple itu1 itu2) (IV_Couple itu1' itu2')
| Le_ival0_Closure :
    forall (x:identifier) (e:expr) (ic ic':ienv),
      le_ienv ic ic'
      -> le_ival0 (IV_Closure x e ic) (IV_Closure x e ic')
| Le_ival0_Rec_Closure :
    forall (x f:identifier) (e:expr) (ic ic':ienv),
      le_ienv ic ic'
      -> le_ival0 (IV_Rec_Closure x f e ic) (IV_Rec_Closure x f e ic')
      (* TODO: faut-il ajouter une condition sur id_f ?
               par exemple : id_f = ideps_of_freevars (Rec f x e) ic *)

with le_ienv : ienv -> ienv -> Prop :=
| Le_ienv_empty :
    le_ienv IEnv_empty IEnv_empty
| Le_ienv_cons :
    forall (x:identifier) (iu iu':ival) (ic ic':ienv),
      le_ival iu iu'
      -> le_ienv ic ic'
      -> le_ienv (IEnv_cons x iu ic) (IEnv_cons x iu' ic')
.

Inductive le_itenv : itenv -> itenv -> Prop :=
| Le_itenv_empty :
    le_itenv ITEnv_empty ITEnv_empty
| Le_itenv_cons :
    forall (x:identifier) (itu itu':itval) (itc itc':itenv),
      le_itval itu itu'
      -> le_itenv itc itc'
      -> le_itenv (ITEnv_cons x itu itc) (ITEnv_cons x itu' itc')
.
         

Definition le_imval (imv1 imv2:imval) :=
  forall (itu1:itval),
    Ensembles.In _ imv1 itu1
    -> exists (itu2:itval),
         In _ imv2 itu2
         /\ le_itval itu1 itu2.

Definition le_imenv (imc1 imc2:imenv) :=
  forall (itc1:itenv),
    Ensembles.In _ imc1 itc1
    -> exists (itc2:itenv),
         In _ imc2 itc2
         /\ le_itenv itc1 itc2.


Ltac tac_le_itval :=
  match goal with
    | |- le_itval (IV _ _) (IV _ _) => apply Le_itval; tac_le_itval
    | |- list_Included _ _ => unfold list_Included; auto; tac_le_itval
    | |- le_ival (IV_ _ _) (IV_ _ _) => apply Le_ival; tac_le_itval
    | |- le_ival0 (IV_Num _) (IV_Num _) => apply Le_ival0_Num; tac_le_itval
    | |- le_ival0 (IV_Bool _) (IV_Bool _) => apply Le_ival0_Bool; tac_le_itval
    | |- le_ival0 (IV_Constr0 _) (IV_Constr0 _) => apply Le_ival0_Constr0; tac_le_itval
    | |- le_ival0 (IV_Constr1 _ _) (IV_Constr1 _ _) => apply Le_ival0_Constr1; tac_le_itval
    | |- le_ival0 (IV_Couple _ _) (IV_Couple _ _) => apply Le_ival0_Couple; tac_le_itval
    | |- le_ival0 (IV_Closure _ _ _) (IV_Closure _ _ _) => apply Le_ival0_Closure; tac_le_itval
    | |- le_ival0 (IV_Rec_Closure _ _ _ _) (IV_Rec_Closure _ _ _ _) => apply Le_ival0_Rec_Closure; tac_le_itval
    | |- le_ienv IEnv_empty IEnv_empty => apply Le_ienv_empty; tac_le_itval
    | |- le_ienv (IEnv_cons _ _ _) (IEnv_cons _ _ _) => apply Le_ienv_cons; tac_le_itval
    | |- le_itenv ITEnv_empty ITEnv_empty => apply Le_itenv_empty; tac_le_itval
    | |- le_itenv (ITEnv_cons _ _ _) (ITEnv_cons _ _ _) => apply Le_itenv_cons; tac_le_itval
    | |- _ => idtac
  end.

Lemma le_ival_refl :
  forall (iu:ival), le_ival iu iu.
Proof.
  apply (ival_ind2 (fun iu => le_ival iu iu)
                   (fun iv => le_ival0 iv iv)
                   (fun ic => le_ienv ic ic));
    intros;
    tac_le_itval; auto.
Qed.

Lemma le_ival0_refl :
  forall (iv:ival0), le_ival0 iv iv.
Proof.
  apply (ival0_ind2 (fun iu => le_ival iu iu)
                   (fun iv => le_ival0 iv iv)
                   (fun ic => le_ienv ic ic));
    intros;
    tac_le_itval; auto.
Qed.

Lemma le_itval_refl :
  forall (itu:itval), le_itval itu itu.
Proof.
  induction itu.
  tac_le_itval.
  apply le_ival_refl.
Qed.

Lemma le_itenv_refl :
  forall (itc:itenv), le_itenv itc itc.
Proof.
  induction itc.
  tac_le_itval.
  apply Le_itenv_cons.
  apply le_itval_refl.
  assumption.
Qed.



Lemma le_itval_to_ival :
  forall (itu itu2:itval),
    le_itval itu itu2
    -> le_ival (itval_to_ival itu) (itval_to_ival itu2).
Proof.
  intros itu itu2 H.

  induction itu.
  inversion H.
  simpl.
  assumption.
Qed.


Lemma le_itenv_to_ienv :
  forall (itc itc2:itenv),
    le_itenv itc itc2
    -> le_ienv (itenv_to_ienv itc) (itenv_to_ienv itc2).
Proof.
  induction itc; intros itc2 H.

  inversion H.
  simpl.
  tac_le_itval.

  inversion H.
  simpl.
  tac_le_itval.
  apply le_itval_to_ival; assumption.
  apply IHitc; assumption.
Qed.


Lemma le_ival_to_itval :
  forall (iu iu2:ival),
    le_ival iu iu2
    -> le_itval (ival_to_itval iu) (ival_to_itval iu2).
Proof.
  induction iu.

  intros iu2 H.
  inversion H.
  unfold ival_to_itval.
  tac_le_itval.
  assumption.
Qed.

Lemma le_ienv_to_itenv :
  forall (ic ic2:ienv),
    le_ienv ic ic2
    -> le_itenv (ienv_to_itenv ic) (ienv_to_itenv ic2).
Proof.
  induction ic; intros ic2 H.
  
  inversion H.
  simpl; tac_le_itval.

  inversion H.
  simpl; tac_le_itval.
  apply le_ival_to_itval; auto.
  apply IHic; auto.
Qed.


Lemma le_ival0_trans :
  forall (iv2 iv iv2_2:ival0),
    le_ival0 iv iv2
    -> le_ival0 iv2 iv2_2
    -> le_ival0 iv iv2_2.
Proof.
  apply (ival0_ind2 (fun iu2 => forall (iu iu2_2:ival),
                                 le_ival iu iu2
                                 -> le_ival iu2 iu2_2
                                 -> le_ival iu iu2_2)
                   (fun iv2 => forall (iv iv2_2:ival0),
                                 le_ival0 iv iv2
                                 -> le_ival0 iv2 iv2_2
                                 -> le_ival0 iv iv2_2)
                   (fun ic2 => forall (ic ic2_2:ienv),
                                 le_ienv ic ic2
                                 -> le_ienv ic2 ic2_2
                                 -> le_ienv ic ic2_2));
  try solve [intros; inversion H; inversion H0; tac_le_itval];
  try solve [intros; inversion H0; inversion H1; tac_le_itval; auto];
  try solve [intros; inversion H1; inversion H2; tac_le_itval; auto].
Qed.  

Lemma le_ival_trans :
  forall (iu2 iu iu2_2:ival),
    le_ival iu iu2
    -> le_ival iu2 iu2_2
    -> le_ival iu iu2_2.
Proof.
  apply (ival_ind2 (fun iu2 => forall (iu iu2_2:ival),
                                 le_ival iu iu2
                                 -> le_ival iu2 iu2_2
                                 -> le_ival iu iu2_2)
                   (fun iv2 => forall (iv iv2_2:ival0),
                                 le_ival0 iv iv2
                                 -> le_ival0 iv2 iv2_2
                                 -> le_ival0 iv iv2_2)
                   (fun ic2 => forall (ic ic2_2:ienv),
                                 le_ienv ic ic2
                                 -> le_ienv ic2 ic2_2
                                 -> le_ienv ic ic2_2));
  try solve [intros; inversion H; inversion H0; tac_le_itval];
  try solve [intros; inversion H0; inversion H1; tac_le_itval; auto];
  try solve [intros; inversion H1; inversion H2; tac_le_itval; auto].
Qed.  

Lemma le_itval_trans :
  forall (itu itu2 itu2_2:itval),
    le_itval itu itu2
    -> le_itval itu2 itu2_2
    -> le_itval itu itu2_2.
Proof.
  intros itu itu2 itu2_2 H H0.

  destruct itu.
  destruct itu2.
  destruct itu2_2.

  inversion H.
  inversion H0.
  tac_le_itval; auto.
  
  apply le_ival_trans with (iu2:=u0); auto.
Qed.

Lemma le_itenv_trans :
  forall (itc itc2 itc2_2:itenv),
    le_itenv itc itc2
    -> le_itenv itc2 itc2_2
    -> le_itenv itc itc2_2.
Proof.
  intros itc itc2 itc2_2.
  revert itc itc2_2.
  induction itc2;
  destruct itc;
  destruct itc2_2;
  intros H H0;
  try solve [inversion H];
  try solve [inversion H0].

  apply Le_itenv_empty.

  inversion H; inversion H0.
  apply Le_itenv_cons; auto.
  apply le_itval_trans with (itu2:=uu); auto.
Qed.


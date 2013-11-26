Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.

Require Import instrumented_values.
Require Import collecting_values.

Require Import imval_order.

Require Import List.
Require Import ensembles.


Definition list_Included {A:Set} (l1 l2:list A) :=
  forall (x:A),
    List.In x l1 -> List.In x l2.



Definition le_ival0s (ivs1 ivs2:Ensemble ival0) :=
  forall (iv1:ival0),
    Ensembles.In _ ivs1 iv1
    -> exists (iv2:ival0),
         In _ ivs2 iv2
         /\ le_ival0 iv1 iv2.

Inductive le_ctval : ctval -> ctval -> Prop :=
| Le_ctval :
    forall (itd1 itd2:itdeps) (id1 id2:ideps) (ivs1 ivs2:Ensemble ival0),
      list_Included itd1 itd2
      -> list_Included id1 id2
      -> le_ival0s ivs1 ivs2
      -> le_ctval (CTVal itd1 id1 ivs1) (CTVal itd2 id2 ivs2)
.


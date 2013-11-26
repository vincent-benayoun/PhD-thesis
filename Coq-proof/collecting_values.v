
Add Rec LoadPath "." as DEP_AI.

Require Import language.

Require Import instrumented_values.

Require Import ensembles.



Inductive ctval : Type :=
| CTVal (td:itdeps) (d:ideps) (ivs:Ensemble ival0) : ctval.

Inductive ctenv : Type :=
| CTEnv_empty : ctenv
| CTEnv_cons (x:identifier) (ctv:ctval) (ctc':ctenv) : ctenv.

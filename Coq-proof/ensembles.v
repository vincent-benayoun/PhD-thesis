
Require Export Ensembles.

Definition SetMap {A B:Type} (f:A->B) (s:Ensemble A) : Ensemble B :=
  fun y => exists x, y = f x /\ In _ s x.

Definition SetMap2 {A B C:Type} (f:A->B->C) (s:Ensemble A) (s':Ensemble B) : Ensemble C :=
  fun z => exists x y, z = f x y /\ In _ s x /\ In _ s' y.

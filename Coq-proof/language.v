
Add Rec LoadPath "." as DEP_AI.

Require Import List.
Require Import Peano_dec.
Require Import Arith.
Require Export ZArith.

Require Import ensembles.
Require Import Finite_sets.

(* identifiers *)
Parameter identifier : Set.
Parameter beq_identifier : identifier -> identifier -> bool.
Parameter beq_identifier_eq : forall n m : identifier, beq_identifier n m = true -> n = m.
Parameter eq_beq_identifier : forall n m : identifier, n = m -> beq_identifier n m = true.
Parameter neq_beq_identifier : forall n m : identifier, n <> m -> beq_identifier n m = false.
Parameter identifier_dec : forall n m : identifier, {n = m} + {n <> m}.

(* names of data constructors *)
Definition constr : Set := nat.

(* labels *)
Parameter label : Set.
Parameter eq_label_dec : forall n m : label, {n = m} + {n <> m}.
Definition eq_label (x y:label) : Prop := x = y.
Definition neq_label (x y:label) : Prop := x <> y.
Parameter eq_label_decide : forall n m : label, {eq_label n m} + {~ eq_label n m}.
Parameter eq_label_eq : forall n m : label, eq_label n m -> n = m.
Parameter eq_eq_label : forall n m : label, n = m -> eq_label n m.
Parameter label_finite_set : forall s : Ensemble label, exists lst : list label,
                               forall l:label, In _ s l <-> List.In l lst.


Inductive pattern : Set := 
 | P_Constr0 : constr -> pattern
 | P_Constr1 : constr -> identifier -> pattern
 | P_Couple  : identifier -> identifier -> pattern.


Inductive expr : Set :=
  | Num :  Z -> expr
  | Constr0 : constr ->  expr
  | Constr1 : constr ->  expr -> expr
  | Var : identifier -> expr
  | Lambda : identifier -> expr -> expr
  | Rec : identifier -> identifier -> expr -> expr
  | Apply : expr -> expr -> expr
  | If : expr -> expr -> expr -> expr
  | Expr_match : expr -> (pattern*expr) -> option (identifier*expr) -> expr
  | Couple : expr -> expr -> expr
  | Annot : label -> expr -> expr   
  | Let_in : identifier -> expr -> expr -> expr.


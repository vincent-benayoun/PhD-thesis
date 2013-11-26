Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.

Require Import over_instrumented_values.
Require Import oitval_val_conversion.


(*----- IN OVER INSTRUMENTED VALUES -----*)

Inductive label_does_not_appear_in_oitdeps : label -> oitdeps -> Prop :=
| Ldna_in_oitdeps_empty :
  forall (l:label),
    label_does_not_appear_in_oitdeps l nil
| Ldna_in_oitdeps_cons :
  forall (l l':label) (f:val->bool) (tl:oitdeps),
    ~(eq l l')
    -> label_does_not_appear_in_oitdeps l tl
    -> label_does_not_appear_in_oitdeps l (cons (l',f) tl).

Inductive label_does_not_appear_in_oideps : label -> oideps -> Prop :=
| Ldna_in_oideps_empty :
  forall (l:label),
    label_does_not_appear_in_oideps l nil
| Ldna_in_oideps_cons :
  forall (l l':label) (f:val->val) (tl:oideps),
    ~(eq l l')
    -> label_does_not_appear_in_oideps l tl
    -> label_does_not_appear_in_oideps l (cons (l',f) tl).


Inductive label_does_not_appear_in_expr : label -> oitenv -> expr -> Prop :=
| Ldna_in_expr_Num :
  forall (l:label) (c:oitenv) (n:Z),
    label_does_not_appear_in_expr l c (Num n)
| Ldna_in_expr_Constr0 :
  forall (l:label) (c:oitenv) (n:constr),
    label_does_not_appear_in_expr l c (Constr0 n)
| Ldna_in_expr_Constr1 :
  forall (l:label) (c:oitenv) (n:constr) (e:expr),
    label_does_not_appear_in_expr l c e
    -> label_does_not_appear_in_expr l c (Constr1 n e)
| Ldna_in_expr_Var :
  forall (l:label) (c:oitenv) (x:identifier) (uu:oitval),
    assoc_ident_in_oitenv x c = Ident_in_oitenv uu
    -> label_does_not_appear_in_oitval l uu
    -> label_does_not_appear_in_expr l c (Var x)
| Ldna_in_expr_Var2 :
  forall (l:label) (c:oitenv) (x:identifier),
    assoc_ident_in_oitenv x c = Ident_not_in_oitenv
    -> label_does_not_appear_in_expr l c (Var x)
| Ldna_in_expr_Lambda :
  forall (l:label) (c:oitenv) (x:identifier) (e:expr),
    label_does_not_appear_in_oitenv l c
    -> label_does_not_appear_in_expr l c e
    -> label_does_not_appear_in_expr l c (Lambda x e)
| Ldna_in_expr_Rec :
  forall (l:label) (c:oitenv) (f x:identifier) (e:expr),
    label_does_not_appear_in_oitenv l c
    -> label_does_not_appear_in_expr l c e
    -> label_does_not_appear_in_expr l c (Rec f x e)
| Ldna_in_expr_Apply :
  forall (l:label) (c:oitenv) (e1 e2:expr),
    label_does_not_appear_in_expr l c e1
    -> label_does_not_appear_in_expr l c e2
    -> label_does_not_appear_in_expr l c (Apply e1 e2)
| Ldna_in_expr_If :
  forall (l:label) (c:oitenv) (e e1 e2:expr),
    label_does_not_appear_in_expr l c e
    -> label_does_not_appear_in_expr l c e1
    -> label_does_not_appear_in_expr l c e2
    -> label_does_not_appear_in_expr l c (If e e1 e2)
| Ldna_in_expr_Expr_match1 :
  forall (l:label) (c:oitenv) (e e1:expr) (p:pattern),
    label_does_not_appear_in_expr l c e
    -> label_does_not_appear_in_expr l c e1
    -> label_does_not_appear_in_expr l c (Expr_match e (p,e1) None)
| Ldna_in_expr_Expr_match2 :
  forall (l:label) (c:oitenv) (e e1 e2:expr) (p:pattern) (x:identifier),
    label_does_not_appear_in_expr l c e
    -> label_does_not_appear_in_expr l c e1
    -> label_does_not_appear_in_expr l c e2
    -> label_does_not_appear_in_expr l c (Expr_match e (p,e1) (Some (x,e2)))   
| Ldna_in_expr_Couple :
  forall (l:label) (c:oitenv) (e1 e2:expr),
    label_does_not_appear_in_expr l c e1
    -> label_does_not_appear_in_expr l c e2
    -> label_does_not_appear_in_expr l c (Couple e1 e2)
| Ldna_in_expr_Annot :
  forall (l l':label) (c:oitenv) (e:expr),
    label_does_not_appear_in_expr l c e
    -> ~(l = l')
    -> label_does_not_appear_in_expr l c (Annot l' e)
| Ldna_in_expr_Let_in :
  forall (l:label) (c:oitenv) (x:identifier) (e1 e2:expr),
    label_does_not_appear_in_expr l c e1
    -> label_does_not_appear_in_expr l c e2
    -> label_does_not_appear_in_expr l c (Let_in x e1 e2)

with label_does_not_appear_in_oitval : label -> oitval -> Prop :=
| Ldna_in_oitval :
  forall (l:label) (td:oitdeps) (u:oival),
  label_does_not_appear_in_oitdeps l td
  -> label_does_not_appear_in_oival l u
  -> label_does_not_appear_in_oitval l (OIV td u)

with label_does_not_appear_in_oival : label -> oival -> Prop :=
| Ldna_in_oival :
  forall (l:label) (d:oideps) (v:oival0),
  label_does_not_appear_in_oideps l d
  -> label_does_not_appear_in_oival0 l v
  -> label_does_not_appear_in_oival l (OIV_ d v)

with label_does_not_appear_in_oival0 : label -> oival0 -> Prop :=
| Ldna_in_oival0_Num :
  forall (l:label) (n:Z),
  label_does_not_appear_in_oival0 l (OIV_Num n)
| Ldna_in_oival0_Bool :
  forall (l:label) (b:bool),
  label_does_not_appear_in_oival0 l (OIV_Bool b)
| Ldna_in_oival0_Constr0 :
  forall (l:label) (n:constr),
  label_does_not_appear_in_oival0 l (OIV_Constr0 n)
| Ldna_in_oival0_Constr1 :
  forall (l:label) (n:constr) (u:oival),
  label_does_not_appear_in_oival l u
  -> label_does_not_appear_in_oival0 l (OIV_Constr1 n u)
| Ldna_in_oival0_Closure :
  forall (l:label) (x:identifier) (e:expr) (c:oienv),
    label_does_not_appear_in_oienv l c
    -> label_does_not_appear_in_expr l (oienv_to_oitenv c) e
    -> label_does_not_appear_in_oival0 l (OIV_Closure x e c)
| Ldna_in_oival0_Rec_Closure :
  forall (l:label) (f x:identifier) (e:expr) (c:oienv),
    label_does_not_appear_in_oienv l c
    -> label_does_not_appear_in_expr l (oienv_to_oitenv c) e
    -> label_does_not_appear_in_oival0 l (OIV_Rec_Closure f x e c)
| Ldna_in_oival0_Couple :
  forall (l:label) (u1 u2:oival),
  label_does_not_appear_in_oival l u1
  -> label_does_not_appear_in_oival l u2
  -> label_does_not_appear_in_oival0 l (OIV_Couple u1 u2)

with label_does_not_appear_in_oienv : label -> oienv -> Prop :=
| Ldna_in_oienv_empty :
  forall (l:label), label_does_not_appear_in_oienv l OIEnv_empty
| Ldna_in_oienv_cons :
  forall (l:label) (c:oienv) (u:oival) (x:identifier),
    label_does_not_appear_in_oienv l c
    -> label_does_not_appear_in_oival l u
    -> label_does_not_appear_in_oienv l (OIEnv_cons x u c)

with label_does_not_appear_in_oitenv : label -> oitenv -> Prop :=
| Ldna_in_oitenv_empty :
  forall (l:label), label_does_not_appear_in_oitenv l OITEnv_empty
| Ldna_in_oitenv_cons :
  forall (l:label) (c:oitenv) (uu:oitval) (x:identifier),
    label_does_not_appear_in_oitenv l c
    -> label_does_not_appear_in_oitval l uu
    -> label_does_not_appear_in_oitenv l (OITEnv_cons x uu c).

Hint Constructors label_does_not_appear_in_oitval : ldna_oitval.
Hint Constructors label_does_not_appear_in_oival : ldna_oival.
Hint Constructors label_does_not_appear_in_oitdeps : ldna_oitdeps.
Hint Constructors label_does_not_appear_in_oideps : ldna_oideps.
Hint Constructors label_does_not_appear_in_oival0 : ldna_oival0.
Hint Constructors label_does_not_appear_in_oienv : ldna_oienv.
Hint Constructors label_does_not_appear_in_expr : ldna_expr.

Hint Constructors label_does_not_appear_in_oitenv : ldna_oitenv.

Scheme ldna_in_oitval_ind2 := Induction for label_does_not_appear_in_oitval Sort Prop
with ldna_in_oival_ind2 := Induction for label_does_not_appear_in_oival Sort Prop
with ldna_in_oival0_ind2 := Induction for label_does_not_appear_in_oival0 Sort Prop
with ldna_in_oienv_ind2 := Induction for label_does_not_appear_in_oienv Sort Prop
with ldna_in_oitenv_ind2 := Induction for label_does_not_appear_in_oitenv Sort Prop
with ldna_in_expr_ind2 := Induction for label_does_not_appear_in_expr Sort Prop.


(*----- IN SIMPLE VALUES -----*)


Inductive label_does_not_appear_in_val : label -> val -> Prop :=
| Ldna_in_val_Num :
  forall (l:label) (n:Z),
    label_does_not_appear_in_val l (V_Num n)
| Ldna_in_val_Bool :
  forall (l:label) (b:bool),
    label_does_not_appear_in_val l (V_Bool b)
| Ldna_in_val_Constr0 :
  forall (l:label) (n:constr),
    label_does_not_appear_in_val l (V_Constr0 n)
| Ldna_in_val_Constr1 :
  forall (l:label) (n:constr) (v:val),
    label_does_not_appear_in_val l v
    -> label_does_not_appear_in_val l (V_Constr1 n v)
| Ldna_in_val_Couple :
  forall (l:label) (v1 v2:val),
    label_does_not_appear_in_val l v1
    -> label_does_not_appear_in_val l v2
    -> label_does_not_appear_in_val l (V_Couple v1 v2)
| Ldna_in_val_Closure :
  forall (l:label) (x:identifier) (e:expr) (c:env),
    label_does_not_appear_in_env l c
    -> label_does_not_appear_in_expr l (env_to_oitenv c) e
    -> label_does_not_appear_in_val l (V_Closure x e c)
| Ldna_in_val_Rec_Closure :
  forall (l:label) (f x:identifier) (e:expr) (c:env),
   label_does_not_appear_in_env l c
    -> label_does_not_appear_in_expr l (env_to_oitenv c) e
    -> label_does_not_appear_in_val l (V_Rec_Closure f x e c)

with label_does_not_appear_in_env : label -> env -> Prop :=
| Ldna_in_env_empty :
  forall (l:label),
    label_does_not_appear_in_env l Env_empty
| Ldna_in_env_cons :
  forall (l:label) (x:identifier) (v:val) (c:env),
    label_does_not_appear_in_val l v
    -> label_does_not_appear_in_env l c
    -> label_does_not_appear_in_env l (Env_cons x v c).

Hint Constructors label_does_not_appear_in_val : ldna_val.
Hint Constructors label_does_not_appear_in_env : ldna_env.

Scheme ldna_in_val_ind2 := Induction for label_does_not_appear_in_val Sort Prop
with ldna_in_env_ind2 := Induction for label_does_not_appear_in_env Sort Prop.

Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.

Require Import over_instrumented_values.
Require Import instrumented_values.
Require Import oival_ival_conversion.
Require Import oitval_val_conversion.
Require Import itval_val_conversion.

Require Import oival_of_correctness. (* is_instantiable_oitenv *)
Require Import is_instantiable_oitval.

Require Import ldna_in.


Inductive label_does_not_appear_in_itdeps : label -> itdeps -> Prop :=
| Ldna_in_itdeps_empty :
  forall (l:label),
    label_does_not_appear_in_itdeps l nil
| Ldna_in_itdeps_cons :
  forall (l l':label) (tl:itdeps),
    ~(eq l l')
    -> label_does_not_appear_in_itdeps l tl
    -> label_does_not_appear_in_itdeps l (cons l' tl).

Inductive label_does_not_appear_in_ideps : label -> ideps -> Prop :=
| Ldna_in_ideps_empty :
  forall (l:label),
    label_does_not_appear_in_ideps l nil
| Ldna_in_ideps_cons :
  forall (l l':label) (tl:itdeps),
    ~(eq l l')
    -> label_does_not_appear_in_ideps l tl
    -> label_does_not_appear_in_ideps l (cons l' tl).


Inductive label_does_not_appear_in_itdeps_of_itenv : label -> itenv -> Prop :=
| Ldna_in_itdeps_of_itenv_empty :
  forall (l:label),
    label_does_not_appear_in_itdeps_of_itenv l ITEnv_empty
| Ldna_in_itdeps_of_itenv_cons :
  forall (l:label) (x:identifier) (itd:itdeps) (iu:ival) (itc:itenv),
    label_does_not_appear_in_itdeps l itd
    -> label_does_not_appear_in_itdeps_of_itenv l itc
    -> label_does_not_appear_in_itdeps_of_itenv l (ITEnv_cons x (IV itd iu) itc).


Inductive label_does_not_appear_in_oitdeps_of_oitenv : label -> oitenv -> Prop :=
| Ldna_in_oitdeps_of_oitenv_empty :
  forall (l:label),
    label_does_not_appear_in_oitdeps_of_oitenv l OITEnv_empty
| Ldna_in_oitdeps_of_oitenv_cons :
  forall (l:label) (x:identifier) (oitd:oitdeps) (oiu:oival) (oitc:oitenv),
    label_does_not_appear_in_oitdeps l oitd
    -> label_does_not_appear_in_oitdeps_of_oitenv l oitc
    -> label_does_not_appear_in_oitdeps_of_oitenv l (OITEnv_cons x (OIV oitd oiu) oitc).


Lemma ldna_in_itdeps_to_oitdeps :
  forall (l:label) (itd:itdeps),
    label_does_not_appear_in_itdeps l itd
    -> label_does_not_appear_in_oitdeps l (itdeps_to_oitdeps itd).
Proof.
  intros l itd H.
  induction H.
  apply Ldna_in_oitdeps_empty.
  apply Ldna_in_oitdeps_cons; auto.
Qed.

Lemma ldna_in_ideps_to_oideps :
  forall (l:label) (id:ideps),
    label_does_not_appear_in_ideps l id
    -> label_does_not_appear_in_oideps l (ideps_to_oideps id).
Proof.
  intros l id H.
  induction H.
  apply Ldna_in_oideps_empty.
  apply Ldna_in_oideps_cons; auto.
Qed.

Lemma ldna_in_oitdeps_of_itenv_to_oitenv :
  forall (l:label) (itc:itenv),
    label_does_not_appear_in_itdeps_of_itenv l itc
    -> label_does_not_appear_in_oitdeps_of_oitenv l (itenv_to_oitenv itc).
Proof.
  intros l itc H.
  induction H.
  apply Ldna_in_oitdeps_of_oitenv_empty.

  apply Ldna_in_oitdeps_of_oitenv_cons; auto.
  apply ldna_in_itdeps_to_oitdeps; auto.
Qed.


Lemma label_does_not_appear_in_oitdeps_of_oitenv_is_instantiable :
  forall (l:label) (vl:val) (oitc:oitenv),
    label_does_not_appear_in_oitdeps_of_oitenv l oitc
    -> is_instantiable_oitenv l vl oitc.
Proof.
  intros l vl oitc H.
  induction H.
  exists Env_empty; auto.

  inversion_clear IHlabel_does_not_appear_in_oitdeps_of_oitenv as [c H_inst_oitc].
  destruct (is_instantiable_oival oiu l vl) as [v H_inst_oiu].
  exists (Env_cons x v c).
  simpl.
  rewrite utils.match_option_bool_not_true.
  rewrite H_inst_oiu.
  rewrite <-H_inst_oitc.
  auto.
  clear H0 c H_inst_oitc v H_inst_oiu oitc oiu x.
  induction H.
  inversion 1.
  simpl.
  destruct (eq_label_dec l l'); auto.
Qed.











Inductive label_does_not_appear_in_itenv_expr : label -> itenv -> expr -> Prop :=
| Ldna_in_itenv_expr_Num :
  forall (l:label) (c:itenv) (n:Z),
    label_does_not_appear_in_itenv_expr l c (Num n)
| Ldna_in_itenv_expr_Constr0 :
  forall (l:label) (c:itenv) (n:constr),
    label_does_not_appear_in_itenv_expr l c (Constr0 n)
| Ldna_in_itenv_expr_Constr1 :
  forall (l:label) (c:itenv) (n:constr) (e:expr),
    label_does_not_appear_in_itenv_expr l c e
    -> label_does_not_appear_in_itenv_expr l c (Constr1 n e)
| Ldna_in_itenv_expr_Var :
  forall (l:label) (c:itenv) (x:identifier) (uu:itval),
    assoc_ident_in_itenv x c = Ident_in_itenv uu
    -> label_does_not_appear_in_itval l uu
    -> label_does_not_appear_in_itenv_expr l c (Var x)
| Ldna_in_itenv_expr_Var2 :
  forall (l:label) (c:itenv) (x:identifier),
    assoc_ident_in_itenv x c = Ident_not_in_itenv
    -> label_does_not_appear_in_itenv_expr l c (Var x)
| Ldna_in_itenv_expr_Lambda :
  forall (l:label) (c:itenv) (x:identifier) (e:expr),
    label_does_not_appear_in_itenv l c
    -> label_does_not_appear_in_itenv_expr l c e
    -> label_does_not_appear_in_itenv_expr l c (Lambda x e)
| Ldna_in_itenv_expr_Rec :
  forall (l:label) (c:itenv) (f x:identifier) (e:expr),
    label_does_not_appear_in_itenv l c
    -> label_does_not_appear_in_itenv_expr l c e
    -> label_does_not_appear_in_itenv_expr l c (Rec f x e)
| Ldna_in_itenv_expr_Apply :
  forall (l:label) (c:itenv) (e1 e2:expr),
    label_does_not_appear_in_itenv_expr l c e1
    -> label_does_not_appear_in_itenv_expr l c e2
    -> label_does_not_appear_in_itenv_expr l c (Apply e1 e2)
| Ldna_in_itenv_expr_If :
  forall (l:label) (c:itenv) (e e1 e2:expr),
    label_does_not_appear_in_itenv_expr l c e
    -> label_does_not_appear_in_itenv_expr l c e1
    -> label_does_not_appear_in_itenv_expr l c e2
    -> label_does_not_appear_in_itenv_expr l c (If e e1 e2)
| Ldna_in_itenv_expr_Expr_match1 :
  forall (l:label) (c:itenv) (e e1:expr) (p:pattern),
    label_does_not_appear_in_itenv_expr l c e
    -> label_does_not_appear_in_itenv_expr l c e1
    -> label_does_not_appear_in_itenv_expr l c (Expr_match e (p,e1) None)
| Ldna_in_itenv_expr_Expr_match2 :
  forall (l:label) (c:itenv) (e e1 e2:expr) (p:pattern) (x:identifier),
    label_does_not_appear_in_itenv_expr l c e
    -> label_does_not_appear_in_itenv_expr l c e1
    -> label_does_not_appear_in_itenv_expr l c e2
    -> label_does_not_appear_in_itenv_expr l c (Expr_match e (p,e1) (Some (x,e2)))   
| Ldna_in_itenv_expr_Couple :
  forall (l:label) (c:itenv) (e1 e2:expr),
    label_does_not_appear_in_itenv_expr l c e1
    -> label_does_not_appear_in_itenv_expr l c e2
    -> label_does_not_appear_in_itenv_expr l c (Couple e1 e2)
| Ldna_in_itenv_expr_Annot :
  forall (l l':label) (c:itenv) (e:expr),
    label_does_not_appear_in_itenv_expr l c e
    -> ~(l = l')
    -> label_does_not_appear_in_itenv_expr l c (Annot l' e)
| Ldna_in_itenv_expr_Let_in :
  forall (l:label) (c:itenv) (x:identifier) (e1 e2:expr),
    label_does_not_appear_in_itenv_expr l c e1
    -> label_does_not_appear_in_itenv_expr l c e2
    -> label_does_not_appear_in_itenv_expr l c (Let_in x e1 e2)

with label_does_not_appear_in_itval : label -> itval -> Prop :=
| Ldna_in_itval :
  forall (l:label) (td:itdeps) (u:ival),
  label_does_not_appear_in_itdeps l td
  -> label_does_not_appear_in_ival l u
  -> label_does_not_appear_in_itval l (IV td u)

with label_does_not_appear_in_ival : label -> ival -> Prop :=
| Ldna_in_ival :
  forall (l:label) (d:ideps) (v:ival0),
  label_does_not_appear_in_ideps l d
  -> label_does_not_appear_in_ival0 l v
  -> label_does_not_appear_in_ival l (IV_ d v)

with label_does_not_appear_in_ival0 : label -> ival0 -> Prop :=
| Ldna_in_ival0_Num :
  forall (l:label) (n:Z),
  label_does_not_appear_in_ival0 l (IV_Num n)
| Ldna_in_ival0_Bool :
  forall (l:label) (b:bool),
  label_does_not_appear_in_ival0 l (IV_Bool b)
| Ldna_in_ival0_Constr0 :
  forall (l:label) (n:constr),
  label_does_not_appear_in_ival0 l (IV_Constr0 n)
| Ldna_in_ival0_Constr1 :
  forall (l:label) (n:constr) (u:ival),
  label_does_not_appear_in_ival l u
  -> label_does_not_appear_in_ival0 l (IV_Constr1 n u)
| Ldna_in_ival0_Closure :
  forall (l:label) (x:identifier) (e:expr) (c:ienv),
    label_does_not_appear_in_ienv l c
    -> label_does_not_appear_in_itenv_expr l (ienv_to_itenv c) e
    -> label_does_not_appear_in_ival0 l (IV_Closure x e c)
| Ldna_in_ival0_Rec_Closure :
  forall (l:label) (f x:identifier) (e:expr) (c:ienv),
    label_does_not_appear_in_ienv l c
    -> label_does_not_appear_in_itenv_expr l (ienv_to_itenv c) e
    -> label_does_not_appear_in_ival0 l (IV_Rec_Closure f x e c)
| Ldna_in_ival0_Couple :
  forall (l:label) (u1 u2:ival),
  label_does_not_appear_in_ival l u1
  -> label_does_not_appear_in_ival l u2
  -> label_does_not_appear_in_ival0 l (IV_Couple u1 u2)

with label_does_not_appear_in_ienv : label -> ienv -> Prop :=
| Ldna_in_ienv_empty :
  forall (l:label), label_does_not_appear_in_ienv l IEnv_empty
| Ldna_in_ienv_cons :
  forall (l:label) (c:ienv) (u:ival) (x:identifier),
    label_does_not_appear_in_ienv l c
    -> label_does_not_appear_in_ival l u
    -> label_does_not_appear_in_ienv l (IEnv_cons x u c)

with label_does_not_appear_in_itenv : label -> itenv -> Prop :=
| Ldna_in_itenv_empty :
  forall (l:label), label_does_not_appear_in_itenv l ITEnv_empty
| Ldna_in_itenv_cons :
  forall (l:label) (c:itenv) (uu:itval) (x:identifier),
    label_does_not_appear_in_itenv l c
    -> label_does_not_appear_in_itval l uu
    -> label_does_not_appear_in_itenv l (ITEnv_cons x uu c).

Hint Constructors label_does_not_appear_in_itval : ldna_itval.
Hint Constructors label_does_not_appear_in_ival : ldna_ival.
Hint Constructors label_does_not_appear_in_itdeps : ldna_itdeps.
Hint Constructors label_does_not_appear_in_ideps : ldna_ideps.
Hint Constructors label_does_not_appear_in_ival0 : ldna_ival0.
Hint Constructors label_does_not_appear_in_ienv : ldna_ienv.
Hint Constructors label_does_not_appear_in_itenv_expr : ldna_expr.

Hint Constructors label_does_not_appear_in_itenv : ldna_itenv.


Scheme ldna_in_itval_ind2 := Induction for label_does_not_appear_in_itval Sort Prop
with ldna_in_ival_ind2 := Induction for label_does_not_appear_in_ival Sort Prop
with ldna_in_ival0_ind2 := Induction for label_does_not_appear_in_ival0 Sort Prop
with ldna_in_ienv_ind2 := Induction for label_does_not_appear_in_ienv Sort Prop
with ldna_in_itenv_ind2 := Induction for label_does_not_appear_in_itenv Sort Prop
with ldna_in_itenv_expr_ind2 := Induction for label_does_not_appear_in_itenv_expr Sort Prop.


Lemma itenv_to_oitenv_via_oienv_or_itenv :
  forall (c:ienv),
    itenv_to_oitenv (ienv_to_itenv c) = oienv_to_oitenv (ienv_to_oienv c).
Proof.
  intros c.
  induction c; auto.

  simpl.
  f_equal; auto.
Qed.

Lemma assoc_in_itenv_to_oitenv :
  forall (c:itenv) (x:identifier) (itu:itval),
    assoc_ident_in_itenv x c = Ident_in_itenv itu
    -> assoc_ident_in_oitenv x (itenv_to_oitenv c) = Ident_in_oitenv (itval_to_oitval itu).
Proof.
  intros c x itu H.
  induction c; inversion H.
  simpl.
  destruct (beq_identifier x x0); auto.
  inversion H1; auto.
Qed.  

Lemma assoc_not_in_itenv_to_oitenv :
  forall (c:itenv) (x:identifier),
    assoc_ident_in_itenv x c = Ident_not_in_itenv
    -> assoc_ident_in_oitenv x (itenv_to_oitenv c) = Ident_not_in_oitenv.
Proof.
  intros c x H.
  induction c; inversion H; auto.
  simpl.
  destruct (beq_identifier x x0); auto.
  inversion H1; auto.
Qed.  

Lemma ldna_in_itval_to_oitval :
  forall (l:label) (itu:itval),
    label_does_not_appear_in_itval l itu
    -> label_does_not_appear_in_oitval l (itval_to_oitval itu).
Proof.
  intros l itu.

  apply (ldna_in_itval_ind2
           (fun l itu P => label_does_not_appear_in_oitval l (itval_to_oitval itu))
           (fun l iu P => label_does_not_appear_in_oival l (ival_to_oival iu))
           (fun l iv P => label_does_not_appear_in_oival0 l (ival0_to_oival0 iv))
           (fun l ic P => label_does_not_appear_in_oienv l (ienv_to_oienv ic))
           (fun l itc P => label_does_not_appear_in_oitenv l (itenv_to_oitenv itc))
           (fun l itc e P => label_does_not_appear_in_expr l (itenv_to_oitenv itc) e));
  intros.
  
  apply Ldna_in_oitval; auto.
  apply ldna_in_itdeps_to_oitdeps; auto.

  apply Ldna_in_oival; auto.
  apply ldna_in_ideps_to_oideps; auto.

  apply Ldna_in_oival0_Num.
  apply Ldna_in_oival0_Bool.
  apply Ldna_in_oival0_Constr0.
  apply Ldna_in_oival0_Constr1.
  destruct u.
  inversion l1.
  inversion H.
  apply Ldna_in_oival; auto.
  apply Ldna_in_oival0_Closure; auto.
  rewrite <-itenv_to_oitenv_via_oienv_or_itenv; auto.
  apply Ldna_in_oival0_Rec_Closure; auto.
  rewrite <-itenv_to_oitenv_via_oienv_or_itenv; auto.
  apply Ldna_in_oival0_Couple; auto.

  apply Ldna_in_oienv_empty.
  apply Ldna_in_oienv_cons; auto.

  apply Ldna_in_oitenv_empty.
  apply Ldna_in_oitenv_cons; auto.

  apply Ldna_in_expr_Num.
  apply Ldna_in_expr_Constr0.
  apply Ldna_in_expr_Constr1; auto.
  apply Ldna_in_expr_Var with (uu:=itval_to_oitval uu); auto.
  apply assoc_in_itenv_to_oitenv; auto.
  apply Ldna_in_expr_Var2; auto.
  apply assoc_not_in_itenv_to_oitenv; auto.
  apply Ldna_in_expr_Lambda; auto.
  apply Ldna_in_expr_Rec; auto.
  apply Ldna_in_expr_Apply; auto.
  apply Ldna_in_expr_If; auto.
  apply Ldna_in_expr_Expr_match1; auto.
  apply Ldna_in_expr_Expr_match2; auto.
  apply Ldna_in_expr_Couple; auto.
  apply Ldna_in_expr_Annot; auto.
  apply Ldna_in_expr_Let_in; auto.
Qed.

Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.
Require Import operational_semantics.

Require Import over_instrumented_values.
Require Import oitval_instantiation.
Require Import oitval_val_conversion.
Require Import oitval_val_conversion_facts.
Require Import over_instrumented_semantics.

Require Import injection_operational_semantics.
Require Import ldna_in.
Require Import ldna_in_facts.
Require Import proof_injection_op_sem.

Require Import instrumented_values.
Require Import instrumented_semantics.
Require Import itval_val_conversion.
Require Import oival_ival_conversion.
Require Import oival_ival_conversion_facts.

(* pour Lemma exists_deps_spec_Apply *)
Require Import oival_of_correctness.

Require Import partially_approximated.
Require Import val_of_with_injection_in_partially_approximated_oitenv.



Require Import FunctionalExtensionality.

Lemma deps_spec_Apply_tf_in_partially_approximated :
  forall (oitu2 oitu2_:oitval) (l:label) (f f_:val->val) (tf' tf'_:val->bool) (f' f'_:val->val),
    deps_spec_Apply_funs oitu2 l f tf' f'
    -> deps_spec_Apply_funs oitu2_ l f_ tf'_ f'_
    -> partially_approximated_oitval oitu2 oitu2_
    -> partially_approximated_oideps_fun f f_
    -> partially_approximated_oitdeps_fun tf' tf'_.
Proof.
  intros oitu2 oitu2_ l f f_ tf' tf'_ f' f'_ H_deps_spec H_deps_spec_ H_papprox_oitu2 H_papprox_f.

  inversion_clear H_papprox_f.
  apply PApprox_oitdeps_fun.
  intros vl.
  specialize (H vl).

  specialize (H_deps_spec vl).
  specialize (H_deps_spec_ vl).

  induction H; inversion_clear H_deps_spec_; auto.

  (* case Closure *)
  rename c' into c_.
  inversion_clear H_deps_spec as [H_exists H_not_exists].
  rename H0 into H_exists_, H1 into H_not_exists_.
  induction (excluded_middle (exists v2 v' : val,
    instantiate_oitval l vl oitu2_ = Some v2 /\
    val_of_with_injection l vl
    (OITEnv_cons x (val_to_oitval v2) (env_to_oitenv c_)) e v')) as [H_ex|H_nex].

  (** there is a value v' for the application *)
  clear H_not_exists_ H_not_exists.
  inversion_clear H_ex as [v2_ HHH];
    inversion_clear HHH as [v'_ HH];
    inversion_clear HH as [H_inst_oitu2_ H_val_of_inj_e_].
  specialize(H_exists_ v2_ v'_ H_inst_oitu2_ H_val_of_inj_e_).

  (*** instantiation of oitu2 *)
  assert(HH_inst_oitu2:=instantiate_partially_approximated_oitval oitu2 oitu2_ l vl v2_ H_papprox_oitu2 H_inst_oitu2_).
  inversion_clear HH_inst_oitu2 as [v2 HH];
    inversion_clear HH as [H_inst_oitu2 H_papprox_v2].

  (*** evaluation of e *)
  assert(HH_val_of_in_e:=val_of_with_injection_in_partially_approximated_oitenv
                           (OITEnv_cons x (val_to_oitval v2) (env_to_oitenv c))
                           (OITEnv_cons x (val_to_oitval v2_) (env_to_oitenv c_))
                           l vl e v'_).
  assert(H_papprox_oitc : partially_approximated_oitenv
                            (OITEnv_cons x (val_to_oitval v2) (env_to_oitenv c))
                            (OITEnv_cons x (val_to_oitval v2_) (env_to_oitenv c_))).
  apply PApprox_oitenv_cons.
  apply partially_approximated_val_to_oitval; auto.
  apply partially_approximated_env_to_oitenv; auto.
  specialize(HH_val_of_in_e H_papprox_oitc H_val_of_inj_e_).

  inversion_clear HH_val_of_in_e as [v' HH];
    inversion_clear HH as [H_val_of_inj_e H_papprox_v'].

  specialize(H_exists v2 v' H_inst_oitu2 H_val_of_inj_e).
  inversion_clear H_exists as [H_tf' H_f'].
  inversion_clear H_exists_ as [H_tf'_ H_f'_].
  right.
  rewrite H_tf'; auto.

  (** there is no value v' for the application *)
  clear H_exists_ H_exists.
  specialize (H_not_exists_ H_nex).
  left; apply H_not_exists_.
  
  (* case Rec_Closure *)
  rename c' into c_.
  inversion_clear H_deps_spec as [H_exists H_not_exists].
  rename H0 into H_exists_, H1 into H_not_exists_.
  induction (excluded_middle (exists v2 v' : val,
                     instantiate_oitval l vl oitu2_ = Some v2 /\
                     val_of_with_injection l vl
                       (env_to_oitenv
                          (add_env f0 (V_Rec_Closure f0 x e c_)
                             (add_env x v2 c_))) e v')) as [H_ex|H_nex].

  (** there is a value v' for the application *)
  clear H_not_exists_ H_not_exists.
  inversion_clear H_ex as [v2_ HHH];
    inversion_clear HHH as [v'_ HH];
    inversion_clear HH as [H_inst_oitu2_ H_val_of_inj_e_].
  specialize(H_exists_ v2_ v'_ H_inst_oitu2_ H_val_of_inj_e_).

  (*** instantiation of oitu2 *)
  assert(HH_inst_oitu2:=instantiate_partially_approximated_oitval oitu2 oitu2_ l vl v2_ H_papprox_oitu2 H_inst_oitu2_).
  inversion_clear HH_inst_oitu2 as [v2 HH];
    inversion_clear HH as [H_inst_oitu2 H_papprox_v2].

  (*** evaluation of e *)
  assert(HH_val_of_in_e:=val_of_with_injection_in_partially_approximated_oitenv
                           (env_to_oitenv (add_env f0 (V_Rec_Closure f0 x e c) (add_env x v2 c)))
                           (env_to_oitenv (add_env f0 (V_Rec_Closure f0 x e c_) (add_env x v2_ c_)))
                           l vl e v'_).
  assert(H_papprox_oitc : partially_approximated_oitenv
                           (env_to_oitenv (add_env f0 (V_Rec_Closure f0 x e c) (add_env x v2 c)))
                           (env_to_oitenv (add_env f0 (V_Rec_Closure f0 x e c_) (add_env x v2_ c_)))).
  apply PApprox_oitenv_cons.
  apply partially_approximated_val_to_oitval.
  apply PApprox_val_Rec_Closure; auto.
  apply partially_approximated_env_to_oitenv; auto.
  apply PApprox_env_cons; auto.
  specialize(HH_val_of_in_e H_papprox_oitc H_val_of_inj_e_).

  inversion_clear HH_val_of_in_e as [v' HH];
    inversion_clear HH as [H_val_of_inj_e H_papprox_v'].

  specialize(H_exists v2 v' H_inst_oitu2 H_val_of_inj_e).
  inversion_clear H_exists as [H_tf' H_f'].
  inversion_clear H_exists_ as [H_tf'_ H_f'_].
  right.
  rewrite H_tf'; auto.

  (** there is no value v' for the application *)
  clear H_exists_ H_exists.
  specialize (H_not_exists_ H_nex).
  left; apply H_not_exists_.
Qed.

Lemma deps_spec_Apply_f_in_partially_approximated :
  forall (oitu2 oitu2_:oitval) (l:label) (f f_:val->val) (tf' tf'_:val->bool) (f' f'_:val->val),
    deps_spec_Apply_funs oitu2 l f tf' f'
    -> deps_spec_Apply_funs oitu2_ l f_ tf'_ f'_
    -> partially_approximated_oitval oitu2 oitu2_
    -> partially_approximated_oideps_fun f f_
    -> partially_approximated_oideps_fun f' f'_.
Proof.
  intros oitu2 oitu2_ l f f_ tf' tf'_ f' f'_ H_deps_spec H_deps_spec_ H_papprox_oitu2 H_papprox_f.

  inversion_clear H_papprox_f.
  apply PApprox_oideps_fun.
  intros vl.
  specialize (H vl).

  specialize (H_deps_spec vl).
  specialize (H_deps_spec_ vl).

  induction H;  inversion_clear H_deps_spec_;
  try rewrite H0; try rewrite H1; try rewrite H2; auto_papprox.

  (* case Closure *)
  rename c' into c_.
  inversion_clear H_deps_spec as [H_exists H_not_exists].
  rename H0 into H_exists_, H1 into H_not_exists_.
  induction (excluded_middle (exists v2 v' : val,
    instantiate_oitval l vl oitu2_ = Some v2 /\
    val_of_with_injection l vl
    (OITEnv_cons x (val_to_oitval v2) (env_to_oitenv c_)) e v')) as [H_ex|H_nex].

  (** there is a value v' for the application *)
  clear H_not_exists_ H_not_exists.
  inversion_clear H_ex as [v2_ HHH];
    inversion_clear HHH as [v'_ HH];
    inversion_clear HH as [H_inst_oitu2_ H_val_of_inj_e_].
  specialize(H_exists_ v2_ v'_ H_inst_oitu2_ H_val_of_inj_e_).

  (*** instantiation of oitu2 *)
  assert(HH_inst_oitu2:=instantiate_partially_approximated_oitval oitu2 oitu2_ l vl v2_ H_papprox_oitu2 H_inst_oitu2_).
  inversion_clear HH_inst_oitu2 as [v2 HH];
    inversion_clear HH as [H_inst_oitu2 H_papprox_v2].

  (*** evaluation of e *)
  assert(HH_val_of_in_e:=val_of_with_injection_in_partially_approximated_oitenv
                           (OITEnv_cons x (val_to_oitval v2) (env_to_oitenv c))
                           (OITEnv_cons x (val_to_oitval v2_) (env_to_oitenv c_))
                           l vl e v'_).
  assert(H_papprox_oitc : partially_approximated_oitenv
                            (OITEnv_cons x (val_to_oitval v2) (env_to_oitenv c))
                            (OITEnv_cons x (val_to_oitval v2_) (env_to_oitenv c_))).
  apply PApprox_oitenv_cons.
  apply partially_approximated_val_to_oitval; auto.
  apply partially_approximated_env_to_oitenv; auto.
  specialize(HH_val_of_in_e H_papprox_oitc H_val_of_inj_e_).

  inversion_clear HH_val_of_in_e as [v' HH];
    inversion_clear HH as [H_val_of_inj_e H_papprox_v'].

  specialize(H_exists v2 v' H_inst_oitu2 H_val_of_inj_e).
  inversion_clear H_exists as [H_tf' H_f'].
  inversion_clear H_exists_ as [H_tf'_ H_f'_].
  rewrite H_f', H_f'_; auto.

  (** there is no value v' for the application *)
  clear H_exists_ H_exists.
  specialize (H_not_exists_ H_nex).
  inversion_clear H_not_exists_ as [H_tf' H_f'].
  rewrite H_f'; auto_papprox.
  
  (* case Rec_Closure *)
  rename c' into c_.
  inversion_clear H_deps_spec as [H_exists H_not_exists].
  rename H0 into H_exists_, H1 into H_not_exists_.
  induction (excluded_middle (exists v2 v' : val,
                     instantiate_oitval l vl oitu2_ = Some v2 /\
                     val_of_with_injection l vl
                       (env_to_oitenv
                          (add_env f0 (V_Rec_Closure f0 x e c_)
                             (add_env x v2 c_))) e v')) as [H_ex|H_nex].

  (** there is a value v' for the application *)
  clear H_not_exists_ H_not_exists.
  inversion_clear H_ex as [v2_ HHH];
    inversion_clear HHH as [v'_ HH];
    inversion_clear HH as [H_inst_oitu2_ H_val_of_inj_e_].
  specialize(H_exists_ v2_ v'_ H_inst_oitu2_ H_val_of_inj_e_).

  (*** instantiation of oitu2 *)
  assert(HH_inst_oitu2:=instantiate_partially_approximated_oitval oitu2 oitu2_ l vl v2_ H_papprox_oitu2 H_inst_oitu2_).
  inversion_clear HH_inst_oitu2 as [v2 HH];
    inversion_clear HH as [H_inst_oitu2 H_papprox_v2].

  (*** evaluation of e *)
  assert(HH_val_of_in_e:=val_of_with_injection_in_partially_approximated_oitenv
                           (env_to_oitenv (add_env f0 (V_Rec_Closure f0 x e c) (add_env x v2 c)))
                           (env_to_oitenv (add_env f0 (V_Rec_Closure f0 x e c_) (add_env x v2_ c_)))
                           l vl e v'_).
  assert(H_papprox_oitc : partially_approximated_oitenv
                           (env_to_oitenv (add_env f0 (V_Rec_Closure f0 x e c) (add_env x v2 c)))
                           (env_to_oitenv (add_env f0 (V_Rec_Closure f0 x e c_) (add_env x v2_ c_)))).
  apply PApprox_oitenv_cons.
  apply partially_approximated_val_to_oitval.
  apply PApprox_val_Rec_Closure; auto.
  apply partially_approximated_env_to_oitenv; auto.
  apply PApprox_env_cons; auto.
  specialize(HH_val_of_in_e H_papprox_oitc H_val_of_inj_e_).

  inversion_clear HH_val_of_in_e as [v' HH];
    inversion_clear HH as [H_val_of_inj_e H_papprox_v'].

  specialize(H_exists v2 v' H_inst_oitu2 H_val_of_inj_e).
  inversion_clear H_exists as [H_tf' H_f'].
  inversion_clear H_exists_ as [H_tf'_ H_f'_].
  rewrite H_f', H_f'_; auto.

  (** there is no value v' for the application *)
  clear H_exists_ H_exists.
  specialize (H_not_exists_ H_nex).
  inversion_clear H_not_exists_ as [H_tf' H_f'].
  rewrite H_f'; auto_papprox.
Qed.


Lemma deps_spec_Apply_in_partially_approximated :
  forall (oitu2 oitu2_:oitval) (oid1 oid1_ oid' oid'_:oideps) (oitd' oitd'_:oitdeps),
    deps_spec_Apply oitu2 oid1 oitd' oid'
    -> deps_spec_Apply oitu2_ oid1_ oitd'_ oid'_
    -> partially_approximated_oitval oitu2 oitu2_
    -> partially_approximated_oideps oid1 oid1_
    -> partially_approximated_oitdeps oitd' oitd'_
       /\ partially_approximated_oideps oid' oid'_.
Proof.
  intros oitu2 oitu2_ oid1.
  revert oitu2 oitu2_.
  
  induction oid1;
    intros oitu2 oitu2_ oid1_ oid' oid'_ oitd' oitd'_ H_deps_spec_Apply H_deps_spec_Apply_ H_oitu2_ H_oid1_.

  (* case oid1 = nil *)
  inversion H_deps_spec_Apply.
  inversion H_oid1_.
  rewrite <-H3 in H_deps_spec_Apply_.
  inversion H_deps_spec_Apply_.
  split; auto_papprox.

  (* case oid1 = cons .. ... *)
  destruct a as [l f].
  inversion H_deps_spec_Apply.
  inversion H_oid1_.
  rewrite <-H9 in H_deps_spec_Apply_.
  inversion H_deps_spec_Apply_.
  specialize(IHoid1 oitu2 oitu2_ oid'1 oid'0 oid'2 oitd'0 oitd'1 H5 H19 H_oitu2_ H11).
  inversion IHoid1.
  split; auto_papprox.

  apply (deps_spec_Apply_tf_in_partially_approximated oitu2 oitu2_ l f f'0) with (f':=f') (f'_:=f'1); auto.
  apply (deps_spec_Apply_f_in_partially_approximated oitu2 oitu2_ l f f'0) with (tf':=tf') (tf'_:=tf'0); auto.
Qed.


Lemma deps_spec_If_tf_in_partially_approximated :
  forall (oitc oitc_:oitenv) (e1 e2:expr) (l:label) (f f_:val->val) (tf' tf'_:val->bool) (f' f'_:val->val),
    deps_spec_If_funs oitc e1 e2 l f tf' f'
    -> deps_spec_If_funs oitc_ e1 e2 l f_ tf'_ f'_
    -> partially_approximated_oitenv oitc oitc_
    -> partially_approximated_oideps_fun f f_
    -> partially_approximated_oitdeps_fun tf' tf'_.
Proof.
  intros oitc oitc_ e1 e2 l f f_ tf' tf'_ f' f'_ H_deps_spec H_deps_spec_ H_papprox_oitc H_papprox_f.

  inversion_clear H_papprox_f.
  apply PApprox_oitdeps_fun.
  intros vl.
  specialize (H vl).

  specialize (H_deps_spec vl).
  specialize (H_deps_spec_ vl).

  induction H; try inversion_clear H_deps_spec_; auto.
  destruct b.

  (* case b = true *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v1 : val, val_of_with_injection l vl oitc_ e1 v1)) as [H_ex|H_nex].

  (** e1 has a value *)
  right; clear H_not_exists.
  inversion_clear H_ex as [v1_ H_val_of_e1_].
  specialize (H_exists v1_ H_val_of_e1_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e1:=val_of_with_injection_in_partially_approximated_oitenv oitc oitc_ l vl e1 v1_
                                                                                 H_papprox_oitc H_val_of_e1_).
  inversion_clear HH_val_of_in_e1 as [v1 HH].
  inversion_clear HH as [H_val_of_e1 H_papprox_v1].
  inversion_clear H_deps_spec.
  specialize (H1 v1 H_val_of_e1).
  inversion_clear H1.
  rewrite H3; auto.

  (** e1 has no value *)
  left; clear H_exists.
  apply H_not_exists; auto.
  
  (* case b = false *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v2 : val, val_of_with_injection l vl oitc_ e2 v2)) as [H_ex|H_nex].

  (** e2 has a value *)
  right; clear H_not_exists.
  inversion_clear H_ex as [v2_ H_val_of_e2_].
  specialize (H_exists v2_ H_val_of_e2_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e2:=val_of_with_injection_in_partially_approximated_oitenv oitc oitc_ l vl e2 v2_
                                                                                 H_papprox_oitc H_val_of_e2_).
  inversion_clear HH_val_of_in_e2 as [v2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v2].
  inversion_clear H_deps_spec.
  specialize (H1 v2 H_val_of_e2).
  inversion_clear H1.
  rewrite H3; auto.

  (** e2 has no value *)
  left; clear H_exists.
  apply H_not_exists; auto.
Qed.

Lemma deps_spec_If_f_in_partially_approximated :
  forall (oitc oitc_:oitenv) (e1 e2:expr) (l:label) (f f_:val->val) (tf' tf'_:val->bool) (f' f'_:val->val),
    deps_spec_If_funs oitc e1 e2 l f tf' f'
    -> deps_spec_If_funs oitc_ e1 e2 l f_ tf'_ f'_
    -> partially_approximated_oitenv oitc oitc_
    -> partially_approximated_oideps_fun f f_
    -> partially_approximated_oideps_fun f' f'_.
Proof.
  intros oitc oitc_ e1 e2 l f f_ tf' tf'_ f' f'_ H_deps_spec H_deps_spec_ H_papprox_oitc H_papprox_f.

  inversion_clear H_papprox_f.
  apply PApprox_oideps_fun.
  intros vl.
  specialize (H vl).

  specialize (H_deps_spec vl).
  specialize (H_deps_spec_ vl).

  induction H; try inversion_clear H_deps_spec_;
  try rewrite H0; try rewrite H1; try rewrite H2; auto_papprox.
  destruct b.

  (* case b = true *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v1 : val, val_of_with_injection l vl oitc_ e1 v1)) as [H_ex|H_nex].

  (** e1 has a value *)
  clear H_not_exists.
  inversion_clear H_ex as [v1_ H_val_of_e1_].
  specialize (H_exists v1_ H_val_of_e1_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e1:=val_of_with_injection_in_partially_approximated_oitenv oitc oitc_ l vl e1 v1_
                                                                                 H_papprox_oitc H_val_of_e1_).
  inversion_clear HH_val_of_in_e1 as [v1 HH].
  inversion_clear HH as [H_val_of_e1 H_papprox_v1].
  inversion_clear H_deps_spec.
  specialize (H1 v1 H_val_of_e1).
  inversion_clear H1.
  rewrite H0, H4; auto.

  (** e1 has no value *)
  clear H_exists.
  specialize (H_not_exists H_nex).
  inversion_clear H_not_exists as [H_tf'_ H_f'_].
  rewrite H_f'_; auto_papprox.
  
  (* case b = false *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v2 : val, val_of_with_injection l vl oitc_ e2 v2)) as [H_ex|H_nex].

  (** e2 has a value *)
  clear H_not_exists.
  inversion_clear H_ex as [v2_ H_val_of_e2_].
  specialize (H_exists v2_ H_val_of_e2_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e2:=val_of_with_injection_in_partially_approximated_oitenv oitc oitc_ l vl e2 v2_
                                                                                 H_papprox_oitc H_val_of_e2_).
  inversion_clear HH_val_of_in_e2 as [v2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v2].
  inversion_clear H_deps_spec.
  specialize (H1 v2 H_val_of_e2).
  inversion_clear H1.
  rewrite H0, H4; auto.

  (** e2 has no value *)
  clear H_exists.
  specialize (H_not_exists H_nex).
  inversion_clear H_not_exists as [H_tf'_ H_f'_].
  rewrite H_f'_; auto_papprox.
Qed.

Lemma deps_spec_If_in_partially_approximated :
  forall (oitc oitc_:oitenv) (e1 e2:expr) (oid oid_ oid' oid'_:oideps) (oitd' oitd'_:oitdeps),
    deps_spec_If oitc e1 e2 oid oitd' oid'
    -> deps_spec_If oitc_ e1 e2 oid_ oitd'_ oid'_
    -> partially_approximated_oitenv oitc oitc_
    -> partially_approximated_oideps oid oid_
    -> partially_approximated_oitdeps oitd' oitd'_
       /\ partially_approximated_oideps oid' oid'_.
Proof.
  intros oitc oitc_ e1 e2 oid.
  revert oitc oitc_ e1 e2.
  
  induction oid;
    intros oitc oitc_ e1 e2 oid_ oid' oid'_ oitd' oitd'_ H_deps_spec_If H_deps_spec_If_ H_oitc_ H_oid_.

  (* case oid1 = nil *)
  inversion H_deps_spec_If.
  inversion H_oid_.
  rewrite <-H5 in H_deps_spec_If_.
  inversion H_deps_spec_If_.
  split; auto_papprox.

  (* case oid1 = cons .. ... *)
  destruct a as [l f].
  inversion H_deps_spec_If.
  inversion H_oid_.
  rewrite <-H11 in H_deps_spec_If_.
  inversion H_deps_spec_If_.
  specialize (IHoid _ _ _ _ _ _ _ _ _ H7 H23 H_oitc_ H13).
  inversion IHoid.
  split; auto_papprox.

  apply (deps_spec_If_tf_in_partially_approximated oitc oitc_ e1 e2 l f f'0) with (f':=f') (f'_:=f'1); auto.
  apply (deps_spec_If_f_in_partially_approximated oitc oitc_ e1 e2 l f f'0) with (tf':=tf') (tf'_:=tf'0); auto.
Qed.


Lemma deps_spec_Match_tf_in_partially_approximated :
  forall (oitc oitc_:oitenv) (p:pattern) (x:identifier) (e1 e2:expr)
         (l:label) (f f_:val->val) (tf' tf'_:val->bool) (f' f'_:val->val),
    deps_spec_Match_funs oitc p x e1 e2 l f tf' f'
    -> deps_spec_Match_funs oitc_ p x e1 e2 l f_ tf'_ f'_
    -> partially_approximated_oitenv oitc oitc_
    -> partially_approximated_oideps_fun f f_
    -> partially_approximated_oitdeps_fun tf' tf'_.
Proof.
  intros oitc oitc_ p x e1 e2 l f f_ tf' tf'_ f' f'_ H_deps_spec H_deps_spec_ H_papprox_oitc H_papprox_f.

  inversion_clear H_papprox_f.
  apply PApprox_oitdeps_fun.
  intros vl.
  specialize (H vl).

  specialize (H_deps_spec vl).
  specialize (H_deps_spec_ vl).

  induction H; try inversion_clear H_deps_spec_; auto;
  simpl in H_deps_spec; simpl in H_deps_spec_.

  (* case Constr0 n *)
  destruct p.
  (** p = Constr0 c *)
  destruct (eq_nat_dec n c).
  (*** n = c *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v1 : val,
                               val_of_with_injection l vl
                                                     (conc_oitenv (env_to_oitenv Env_empty) oitc_) e1 v1)) as [H_ex|H_nex].
  (**** e1 has a value *)
  right; clear H_not_exists.
  inversion_clear H_ex as [v1_ H_val_of_e1_].
  specialize (H_exists v1_ H_val_of_e1_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e1:=val_of_with_injection_in_partially_approximated_oitenv oitc oitc_ l vl e1 v1_
                                                                                 H_papprox_oitc H_val_of_e1_).
  inversion_clear HH_val_of_in_e1 as [v1 HH].
  inversion_clear HH as [H_val_of_e1 H_papprox_v1].
  inversion_clear H_deps_spec.
  specialize (H1 v1 H_val_of_e1).
  inversion_clear H1.
  rewrite H3; auto.
  (**** e1 has no value *)
  left; clear H_exists.
  apply H_not_exists; auto.

  (*** n <> c *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v2 : val,
                               val_of_with_injection l vl
                                                     (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc_) e2 v2)) as [H_ex|H_nex].
  (*** e2 has a value *)
  right; clear H_not_exists.
  inversion_clear H_ex as [v2_ H_val_of_e2_].
  specialize (H_exists v2_ H_val_of_e2_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e2:=val_of_with_injection_in_partially_approximated_oitenv 
                            (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc)
                            (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc_)
                            l vl e2 v2_).
  assert(HH:partially_approximated_oitenv
              (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc)
              (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc_)); auto_papprox.
  specialize (HH_val_of_in_e2 HH H_val_of_e2_).
  clear HH.
  inversion_clear HH_val_of_in_e2 as [v2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v2].
  inversion_clear H_deps_spec.
  specialize (H1 v2 H_val_of_e2).
  inversion_clear H1.
  rewrite H3; auto.
  (*** e2 has no value *)
  left; clear H_exists.
  apply H_not_exists; auto.

  (** p = Constr1 *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v2 : val,
                               val_of_with_injection l vl
                                                     (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc_) e2 v2)) as [H_ex|H_nex].
  (*** e2 has a value *)
  right; clear H_not_exists.
  inversion_clear H_ex as [v2_ H_val_of_e2_].
  specialize (H_exists v2_ H_val_of_e2_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e2:=val_of_with_injection_in_partially_approximated_oitenv 
                            (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc)
                            (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc_)
                            l vl e2 v2_).
  assert(HH:partially_approximated_oitenv
              (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc)
              (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc_)); auto_papprox.
  specialize (HH_val_of_in_e2 HH H_val_of_e2_).
  clear HH.
  inversion_clear HH_val_of_in_e2 as [v2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v2].
  inversion_clear H_deps_spec.
  specialize (H1 v2 H_val_of_e2).
  inversion_clear H1.
  rewrite H3; auto.
  (*** e2 has no value *)
  left; clear H_exists.
  apply H_not_exists; auto.
  (** p = Couple *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v2 : val,
                               val_of_with_injection l vl
                                                     (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc_) e2 v2)) as [H_ex|H_nex].
  (*** e2 has a value *)
  right; clear H_not_exists.
  inversion_clear H_ex as [v2_ H_val_of_e2_].
  specialize (H_exists v2_ H_val_of_e2_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e2:=val_of_with_injection_in_partially_approximated_oitenv 
                            (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc)
                            (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc_)
                            l vl e2 v2_).
  assert(HH:partially_approximated_oitenv
              (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc)
              (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc_)); auto_papprox.
  specialize (HH_val_of_in_e2 HH H_val_of_e2_).
  clear HH.
  inversion_clear HH_val_of_in_e2 as [v2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v2].
  inversion_clear H_deps_spec.
  specialize (H1 v2 H_val_of_e2).
  inversion_clear H1.
  rewrite H3; auto.
  (*** e2 has no value *)
  left; clear H_exists.
  apply H_not_exists; auto.
  
  (* case Constr1 *)
  clear IHpartially_approximated_val.
  destruct p.
  (** p = Constr0 c *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v2 : val,
                               val_of_with_injection l vl
                                                     (OITEnv_cons x (val_to_oitval (V_Constr1 n v')) oitc_) e2 v2)) as [H_ex|H_nex].
  (*** e2 has a value *)
  right; clear H_not_exists.
  inversion_clear H_ex as [v2_ H_val_of_e2_].
  specialize (H_exists v2_ H_val_of_e2_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e2:=val_of_with_injection_in_partially_approximated_oitenv 
                            (OITEnv_cons x (val_to_oitval (V_Constr1 n v)) oitc)
                            (OITEnv_cons x (val_to_oitval (V_Constr1 n v')) oitc_)
                            l vl e2 v2_).
  assert(HH:partially_approximated_oitenv
              (OITEnv_cons x (val_to_oitval (V_Constr1 n v)) oitc)
              (OITEnv_cons x (val_to_oitval (V_Constr1 n v')) oitc_)); auto_papprox.
  apply partially_approximated_val_to_oival; auto.
  specialize (HH_val_of_in_e2 HH H_val_of_e2_).
  clear HH.
  inversion_clear HH_val_of_in_e2 as [v2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v2].
  inversion_clear H_deps_spec.
  specialize (H2 v2 H_val_of_e2).
  inversion_clear H2 as [H_tf' H_f'].
  rewrite H_tf'; auto.
  (*** e2 has no value *)
  left; clear H_exists.
  apply H_not_exists; auto.

  (** p = Constr1 *)
  destruct (eq_nat_dec n c).
  (*** n = c *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v1 : val,
                               val_of_with_injection l vl
                                                     (conc_oitenv (env_to_oitenv (Env_cons i v' Env_empty)) oitc_) e1 v1)) as [H_ex|H_nex].
  (**** e1 has a value *)
  right; clear H_not_exists.
  inversion_clear H_ex as [v1_ H_val_of_e1_].
  specialize (H_exists v1_ H_val_of_e1_).
  inversion_clear H_exists.
  simpl in H_deps_spec; simpl in H_val_of_e1_.
  assert(HH_val_of_in_e1:=val_of_with_injection_in_partially_approximated_oitenv
                            (OITEnv_cons i (val_to_oitval v) oitc)
                            (OITEnv_cons i (val_to_oitval v') oitc_)
                            l vl e1 v1_).
  assert(HH:partially_approximated_oitenv (OITEnv_cons i (val_to_oitval v) oitc)
                                          (OITEnv_cons i (val_to_oitval v') oitc_)); auto_papprox.
  apply partially_approximated_val_to_oival; auto.
  specialize (HH_val_of_in_e1 HH H_val_of_e1_).
  clear HH.
  inversion_clear HH_val_of_in_e1 as [v1 HH].
  inversion_clear HH as [H_val_of_e1 H_papprox_v1].
  inversion_clear H_deps_spec.
  specialize (H2 v1 H_val_of_e1).
  inversion_clear H2 as [H_tf' H_f'].
  rewrite H_tf'; auto.
  (**** e1 has no value *)
  left; clear H_exists.
  apply H_not_exists; auto.
  (*** n <> c *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v2 : val,
                               val_of_with_injection l vl
                                                     (OITEnv_cons x (val_to_oitval (V_Constr1 n v')) oitc_) e2 v2)) as [H_ex|H_nex].
  (*** e2 has a value *)
  right; clear H_not_exists.
  inversion_clear H_ex as [v2_ H_val_of_e2_].
  specialize (H_exists v2_ H_val_of_e2_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e2:=val_of_with_injection_in_partially_approximated_oitenv 
                            (OITEnv_cons x (val_to_oitval (V_Constr1 n v)) oitc)
                            (OITEnv_cons x (val_to_oitval (V_Constr1 n v')) oitc_)
                            l vl e2 v2_).
  assert(HH:partially_approximated_oitenv
              (OITEnv_cons x (val_to_oitval (V_Constr1 n v)) oitc)
              (OITEnv_cons x (val_to_oitval (V_Constr1 n v')) oitc_)); auto_papprox.
  apply partially_approximated_val_to_oival; auto.
  specialize (HH_val_of_in_e2 HH H_val_of_e2_).
  clear HH.
  inversion_clear HH_val_of_in_e2 as [v2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v2].
  inversion_clear H_deps_spec.
  specialize (H2 v2 H_val_of_e2).
  inversion_clear H2 as [H_tf' H_f'].
  rewrite H_tf'; auto.
  (*** e2 has no value *)
  left; clear H_exists.
  apply H_not_exists; auto.
  (** p = Couple *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v2 : val,
                               val_of_with_injection l vl
                                                     (OITEnv_cons x (val_to_oitval (V_Constr1 n v')) oitc_) e2 v2)) as [H_ex|H_nex].
  (*** e2 has a value *)
  right; clear H_not_exists.
  inversion_clear H_ex as [v2_ H_val_of_e2_].
  specialize (H_exists v2_ H_val_of_e2_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e2:=val_of_with_injection_in_partially_approximated_oitenv 
                            (OITEnv_cons x (val_to_oitval (V_Constr1 n v)) oitc)
                            (OITEnv_cons x (val_to_oitval (V_Constr1 n v')) oitc_)
                            l vl e2 v2_).
  assert(HH:partially_approximated_oitenv
              (OITEnv_cons x (val_to_oitval (V_Constr1 n v)) oitc)
              (OITEnv_cons x (val_to_oitval (V_Constr1 n v')) oitc_)); auto_papprox.
  apply partially_approximated_val_to_oival; auto.
  specialize (HH_val_of_in_e2 HH H_val_of_e2_).
  clear HH.
  inversion_clear HH_val_of_in_e2 as [v2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v2].
  inversion_clear H_deps_spec.
  specialize (H2 v2 H_val_of_e2).
  inversion_clear H2 as [H_tf' H_f'].
  rewrite H_tf'; auto.
  (*** e2 has no value *)
  left; clear H_exists.
  apply H_not_exists; auto.


  (* case Couple *)
  clear IHpartially_approximated_val1 IHpartially_approximated_val2.
  destruct p.
  (** p = Constr0 *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v2 : val,
                               val_of_with_injection l vl
                                                     (OITEnv_cons x (val_to_oitval (V_Couple v1' v2')) oitc_) e2 v2)) as [H_ex|H_nex].
  (*** e2 has a value *)
  right; clear H_not_exists.
  inversion_clear H_ex as [v2_ H_val_of_e2_].
  specialize (H_exists v2_ H_val_of_e2_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e2:=val_of_with_injection_in_partially_approximated_oitenv 
                            (OITEnv_cons x (val_to_oitval (V_Couple v1 v2)) oitc)
                            (OITEnv_cons x (val_to_oitval (V_Couple v1' v2')) oitc_)
                            l vl e2 v2_).
  assert(HH:partially_approximated_oitenv
              (OITEnv_cons x (val_to_oitval (V_Couple v1 v2)) oitc)
              (OITEnv_cons x (val_to_oitval (V_Couple v1' v2')) oitc_)); auto_papprox.
  apply partially_approximated_val_to_oival; auto.
  apply partially_approximated_val_to_oival; auto.
  specialize (HH_val_of_in_e2 HH H_val_of_e2_).
  clear HH.
  inversion_clear HH_val_of_in_e2 as [vv2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v2].
  inversion_clear H_deps_spec.
  specialize (H3 vv2 H_val_of_e2).
  inversion_clear H3 as [H_tf' H_f'].
  rewrite H_tf'; auto.
  (*** e2 has no value *)
  left; clear H_exists.
  apply H_not_exists; auto.

  (** p = Constr1 *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v2 : val,
                               val_of_with_injection l vl
                                                     (OITEnv_cons x (val_to_oitval (V_Couple v1' v2')) oitc_) e2 v2)) as [H_ex|H_nex].
  (*** e2 has a value *)
  right; clear H_not_exists.
  inversion_clear H_ex as [v2_ H_val_of_e2_].
  specialize (H_exists v2_ H_val_of_e2_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e2:=val_of_with_injection_in_partially_approximated_oitenv 
                            (OITEnv_cons x (val_to_oitval (V_Couple v1 v2)) oitc)
                            (OITEnv_cons x (val_to_oitval (V_Couple v1' v2')) oitc_)
                            l vl e2 v2_).
  assert(HH:partially_approximated_oitenv
              (OITEnv_cons x (val_to_oitval (V_Couple v1 v2)) oitc)
              (OITEnv_cons x (val_to_oitval (V_Couple v1' v2')) oitc_)); auto_papprox.
  apply partially_approximated_val_to_oival; auto.
  apply partially_approximated_val_to_oival; auto.
  specialize (HH_val_of_in_e2 HH H_val_of_e2_).
  clear HH.
  inversion_clear HH_val_of_in_e2 as [vv2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v2].
  inversion_clear H_deps_spec.
  specialize (H3 vv2 H_val_of_e2).
  inversion_clear H3 as [H_tf' H_f'].
  rewrite H_tf'; auto.
  (*** e2 has no value *)
  left; clear H_exists.
  apply H_not_exists; auto.

  (** p = Couple *)
  simpl in H_deps_spec; simpl in H_deps_spec_.
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v1 : val,
                    val_of_with_injection l vl
                      (OITEnv_cons i (val_to_oitval v1')
                         (OITEnv_cons i0 (val_to_oitval v2') oitc_)) e1 v1)) as [H_ex|H_nex].
  (**** e1 has a value *)
  right; clear H_not_exists.
  inversion_clear H_ex as [v1_ H_val_of_e1_].
  specialize (H_exists v1_ H_val_of_e1_).
  inversion_clear H_exists.
  simpl in H_deps_spec; simpl in H_val_of_e1_.
  assert(HH_val_of_in_e1:=val_of_with_injection_in_partially_approximated_oitenv
                            (OITEnv_cons i (val_to_oitval v1) (OITEnv_cons i0 (val_to_oitval v2) oitc))
                            (OITEnv_cons i (val_to_oitval v1') (OITEnv_cons i0 (val_to_oitval v2') oitc_))
                            l vl e1 v1_).
  assert(HH:partially_approximated_oitenv (OITEnv_cons i (val_to_oitval v1) (OITEnv_cons i0 (val_to_oitval v2) oitc))
                                          (OITEnv_cons i (val_to_oitval v1') (OITEnv_cons i0 (val_to_oitval v2') oitc_))); auto_papprox.
  apply partially_approximated_val_to_oival; auto.
  apply partially_approximated_val_to_oival; auto.
  specialize (HH_val_of_in_e1 HH H_val_of_e1_).
  clear HH.
  inversion_clear HH_val_of_in_e1 as [vv1 HH].
  inversion_clear HH as [H_val_of_e1 H_papprox_v1].
  inversion_clear H_deps_spec.
  specialize (H3 vv1 H_val_of_e1).
  inversion_clear H3 as [H_tf' H_f'].
  rewrite H_tf'; auto.
  (**** e1 has no value *)
  left; clear H_exists.
  apply H_not_exists; auto.
Qed.

Lemma deps_spec_Match_f_in_partially_approximated :
  forall (oitc oitc_:oitenv) (p:pattern) (x:identifier) (e1 e2:expr)
         (l:label) (f f_:val->val) (tf' tf'_:val->bool) (f' f'_:val->val),
    deps_spec_Match_funs oitc p x e1 e2 l f tf' f'
    -> deps_spec_Match_funs oitc_ p x e1 e2 l f_ tf'_ f'_
    -> partially_approximated_oitenv oitc oitc_
    -> partially_approximated_oideps_fun f f_
    -> partially_approximated_oideps_fun f' f'_.
Proof.
  intros oitc oitc_ p x e1 e2 l f f_ tf' tf'_ f' f'_ H_deps_spec H_deps_spec_ H_papprox_oitc H_papprox_f.

  inversion_clear H_papprox_f.
  apply PApprox_oideps_fun.
  intros vl.
  specialize (H vl).

  specialize (H_deps_spec vl).
  specialize (H_deps_spec_ vl).

  induction H; try inversion_clear H_deps_spec_; auto;
  try rewrite H0; try rewrite H1; try rewrite H2; auto_papprox;
  simpl in H_deps_spec; simpl in H_deps_spec_.

  (* case Constr0 n *)
  destruct p.
  (** p = Constr0 c *)
  destruct (eq_nat_dec n c).
  (*** n = c *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v1 : val,
                               val_of_with_injection l vl
                                                     (conc_oitenv (env_to_oitenv Env_empty) oitc_) e1 v1)) as [H_ex|H_nex].
  (**** e1 has a value *)
  clear H_not_exists.
  inversion_clear H_ex as [v1_ H_val_of_e1_].
  specialize (H_exists v1_ H_val_of_e1_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e1:=val_of_with_injection_in_partially_approximated_oitenv oitc oitc_ l vl e1 v1_
                                                                                 H_papprox_oitc H_val_of_e1_).
  inversion_clear HH_val_of_in_e1 as [v1 HH].
  inversion_clear HH as [H_val_of_e1 H_papprox_v1].
  inversion_clear H_deps_spec.
  specialize (H1 v1 H_val_of_e1).
  inversion_clear H1.
  rewrite H0, H4; auto_papprox.
  (**** e1 has no value *)
  clear H_exists.
  specialize (H_not_exists H_nex).
  inversion_clear H_not_exists as [H_tf'_ H_f'_].
  rewrite H_f'_; auto_papprox.

  (*** n <> c *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v2 : val,
                               val_of_with_injection l vl
                                                     (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc_) e2 v2)) as [H_ex|H_nex].
  (*** e2 has a value *)
  clear H_not_exists.
  inversion_clear H_ex as [v2_ H_val_of_e2_].
  specialize (H_exists v2_ H_val_of_e2_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e2:=val_of_with_injection_in_partially_approximated_oitenv 
                            (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc)
                            (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc_)
                            l vl e2 v2_).
  assert(HH:partially_approximated_oitenv
              (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc)
              (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc_)); auto_papprox.
  specialize (HH_val_of_in_e2 HH H_val_of_e2_).
  clear HH.
  inversion_clear HH_val_of_in_e2 as [v2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v2].
  inversion_clear H_deps_spec.
  specialize (H1 v2 H_val_of_e2).
  inversion_clear H1.
  rewrite H0, H4; auto_papprox.
  (*** e2 has no value *)
  clear H_exists.
  specialize (H_not_exists H_nex).
  inversion_clear H_not_exists as [H_tf'_ H_f'_].
  rewrite H_f'_; auto_papprox.

  (** p = Constr1 *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v2 : val,
                               val_of_with_injection l vl
                                                     (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc_) e2 v2)) as [H_ex|H_nex].
  (*** e2 has a value *)
  clear H_not_exists.
  inversion_clear H_ex as [v2_ H_val_of_e2_].
  specialize (H_exists v2_ H_val_of_e2_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e2:=val_of_with_injection_in_partially_approximated_oitenv 
                            (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc)
                            (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc_)
                            l vl e2 v2_).
  assert(HH:partially_approximated_oitenv
              (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc)
              (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc_)); auto_papprox.
  specialize (HH_val_of_in_e2 HH H_val_of_e2_).
  clear HH.
  inversion_clear HH_val_of_in_e2 as [v2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v2].
  inversion_clear H_deps_spec.
  specialize (H1 v2 H_val_of_e2).
  inversion_clear H1.
  rewrite H0, H4; auto_papprox.
  (*** e2 has no value *)
  clear H_exists.
  specialize (H_not_exists H_nex).
  inversion_clear H_not_exists as [H_tf'_ H_f'_].
  rewrite H_f'_; auto_papprox.

  (** p = Couple *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v2 : val,
                               val_of_with_injection l vl
                                                     (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc_) e2 v2)) as [H_ex|H_nex].
  (*** e2 has a value *)
  clear H_not_exists.
  inversion_clear H_ex as [v2_ H_val_of_e2_].
  specialize (H_exists v2_ H_val_of_e2_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e2:=val_of_with_injection_in_partially_approximated_oitenv 
                            (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc)
                            (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc_)
                            l vl e2 v2_).
  assert(HH:partially_approximated_oitenv
              (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc)
              (OITEnv_cons x (val_to_oitval (V_Constr0 n)) oitc_)); auto_papprox.
  specialize (HH_val_of_in_e2 HH H_val_of_e2_).
  clear HH.
  inversion_clear HH_val_of_in_e2 as [v2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v2].
  inversion_clear H_deps_spec.
  specialize (H1 v2 H_val_of_e2).
  inversion_clear H1.
  rewrite H0, H4; auto_papprox.
  (*** e2 has no value *)
  clear H_exists.
  specialize (H_not_exists H_nex).
  inversion_clear H_not_exists as [H_tf'_ H_f'_].
  rewrite H_f'_; auto_papprox.
  
  (* case Constr1 *)
  clear IHpartially_approximated_val.
  destruct p.
  (** p = Constr0 c *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v2 : val,
                               val_of_with_injection l vl
                                                     (OITEnv_cons x (val_to_oitval (V_Constr1 n v')) oitc_) e2 v2)) as [H_ex|H_nex].
  (*** e2 has a value *)
  clear H_not_exists.
  inversion_clear H_ex as [v2_ H_val_of_e2_].
  specialize (H_exists v2_ H_val_of_e2_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e2:=val_of_with_injection_in_partially_approximated_oitenv 
                            (OITEnv_cons x (val_to_oitval (V_Constr1 n v)) oitc)
                            (OITEnv_cons x (val_to_oitval (V_Constr1 n v')) oitc_)
                            l vl e2 v2_).
  assert(HH:partially_approximated_oitenv
              (OITEnv_cons x (val_to_oitval (V_Constr1 n v)) oitc)
              (OITEnv_cons x (val_to_oitval (V_Constr1 n v')) oitc_)); auto_papprox.
  apply partially_approximated_val_to_oival; auto.
  specialize (HH_val_of_in_e2 HH H_val_of_e2_).
  clear HH.
  inversion_clear HH_val_of_in_e2 as [v2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v2].
  inversion_clear H_deps_spec.
  specialize (H2 v2 H_val_of_e2).
  inversion_clear H2 as [H_tf' H_f'].
  rewrite H1, H_f'; auto_papprox.
  (*** e2 has no value *)
  clear H_exists.
  specialize (H_not_exists H_nex).
  inversion_clear H_not_exists as [H_tf'_ H_f'_].
  rewrite H_f'_; auto_papprox.

  (** p = Constr1 *)
  destruct (eq_nat_dec n c).
  (*** n = c *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v1 : val,
                               val_of_with_injection l vl
                                                     (conc_oitenv (env_to_oitenv (Env_cons i v' Env_empty)) oitc_) e1 v1)) as [H_ex|H_nex].
  (**** e1 has a value *)
  clear H_not_exists.
  inversion_clear H_ex as [v1_ H_val_of_e1_].
  specialize (H_exists v1_ H_val_of_e1_).
  inversion_clear H_exists.
  simpl in H_deps_spec; simpl in H_val_of_e1_.
  assert(HH_val_of_in_e1:=val_of_with_injection_in_partially_approximated_oitenv
                            (OITEnv_cons i (val_to_oitval v) oitc)
                            (OITEnv_cons i (val_to_oitval v') oitc_)
                            l vl e1 v1_).
  assert(HH:partially_approximated_oitenv (OITEnv_cons i (val_to_oitval v) oitc)
                                          (OITEnv_cons i (val_to_oitval v') oitc_)); auto_papprox.
  apply partially_approximated_val_to_oival; auto.
  specialize (HH_val_of_in_e1 HH H_val_of_e1_).
  clear HH.
  inversion_clear HH_val_of_in_e1 as [v1 HH].
  inversion_clear HH as [H_val_of_e1 H_papprox_v1].
  inversion_clear H_deps_spec.
  specialize (H2 v1 H_val_of_e1).
  inversion_clear H2 as [H_tf' H_f'].
  rewrite H1, H_f'; auto_papprox.
  (**** e1 has no value *)
  clear H_exists.
  specialize (H_not_exists H_nex).
  inversion_clear H_not_exists as [H_tf'_ H_f'_].
  rewrite H_f'_; auto_papprox.

  (*** n <> c *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v2 : val,
                               val_of_with_injection l vl
                                                     (OITEnv_cons x (val_to_oitval (V_Constr1 n v')) oitc_) e2 v2)) as [H_ex|H_nex].
  (*** e2 has a value *)
  clear H_not_exists.
  inversion_clear H_ex as [v2_ H_val_of_e2_].
  specialize (H_exists v2_ H_val_of_e2_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e2:=val_of_with_injection_in_partially_approximated_oitenv 
                            (OITEnv_cons x (val_to_oitval (V_Constr1 n v)) oitc)
                            (OITEnv_cons x (val_to_oitval (V_Constr1 n v')) oitc_)
                            l vl e2 v2_).
  assert(HH:partially_approximated_oitenv
              (OITEnv_cons x (val_to_oitval (V_Constr1 n v)) oitc)
              (OITEnv_cons x (val_to_oitval (V_Constr1 n v')) oitc_)); auto_papprox.
  apply partially_approximated_val_to_oival; auto.
  specialize (HH_val_of_in_e2 HH H_val_of_e2_).
  clear HH.
  inversion_clear HH_val_of_in_e2 as [v2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v2].
  inversion_clear H_deps_spec.
  specialize (H2 v2 H_val_of_e2).
  inversion_clear H2 as [H_tf' H_f'].
  rewrite H1, H_f'; auto_papprox.
  (*** e2 has no value *)
  clear H_exists.
  specialize (H_not_exists H_nex).
  inversion_clear H_not_exists as [H_tf'_ H_f'_].
  rewrite H_f'_; auto_papprox.

  (** p = Couple *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v2 : val,
                               val_of_with_injection l vl
                                                     (OITEnv_cons x (val_to_oitval (V_Constr1 n v')) oitc_) e2 v2)) as [H_ex|H_nex].
  (*** e2 has a value *)
  clear H_not_exists.
  inversion_clear H_ex as [v2_ H_val_of_e2_].
  specialize (H_exists v2_ H_val_of_e2_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e2:=val_of_with_injection_in_partially_approximated_oitenv 
                            (OITEnv_cons x (val_to_oitval (V_Constr1 n v)) oitc)
                            (OITEnv_cons x (val_to_oitval (V_Constr1 n v')) oitc_)
                            l vl e2 v2_).
  assert(HH:partially_approximated_oitenv
              (OITEnv_cons x (val_to_oitval (V_Constr1 n v)) oitc)
              (OITEnv_cons x (val_to_oitval (V_Constr1 n v')) oitc_)); auto_papprox.
  apply partially_approximated_val_to_oival; auto.
  specialize (HH_val_of_in_e2 HH H_val_of_e2_).
  clear HH.
  inversion_clear HH_val_of_in_e2 as [v2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v2].
  inversion_clear H_deps_spec.
  specialize (H2 v2 H_val_of_e2).
  inversion_clear H2 as [H_tf' H_f'].
  rewrite H1, H_f'; auto_papprox.
  (*** e2 has no value *)
  clear H_exists.
  specialize (H_not_exists H_nex).
  inversion_clear H_not_exists as [H_tf'_ H_f'_].
  rewrite H_f'_; auto_papprox.

  (* case Couple *)
  clear IHpartially_approximated_val1 IHpartially_approximated_val2.
  destruct p.
  (** p = Constr0 *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v2 : val,
                               val_of_with_injection l vl
                                                     (OITEnv_cons x (val_to_oitval (V_Couple v1' v2')) oitc_) e2 v2)) as [H_ex|H_nex].
  (*** e2 has a value *)
  clear H_not_exists.
  inversion_clear H_ex as [v2_ H_val_of_e2_].
  specialize (H_exists v2_ H_val_of_e2_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e2:=val_of_with_injection_in_partially_approximated_oitenv 
                            (OITEnv_cons x (val_to_oitval (V_Couple v1 v2)) oitc)
                            (OITEnv_cons x (val_to_oitval (V_Couple v1' v2')) oitc_)
                            l vl e2 v2_).
  assert(HH:partially_approximated_oitenv
              (OITEnv_cons x (val_to_oitval (V_Couple v1 v2)) oitc)
              (OITEnv_cons x (val_to_oitval (V_Couple v1' v2')) oitc_)); auto_papprox.
  apply partially_approximated_val_to_oival; auto.
  apply partially_approximated_val_to_oival; auto.
  specialize (HH_val_of_in_e2 HH H_val_of_e2_).
  clear HH.
  inversion_clear HH_val_of_in_e2 as [vv2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v2].
  inversion_clear H_deps_spec.
  specialize (H3 vv2 H_val_of_e2).
  inversion_clear H3 as [H_tf' H_f'].
  rewrite H2, H_f'; auto_papprox.
  (*** e2 has no value *)
  clear H_exists.
  specialize (H_not_exists H_nex).
  inversion_clear H_not_exists as [H_tf'_ H_f'_].
  rewrite H_f'_; auto_papprox.

  (** p = Constr1 *)
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v2 : val,
                               val_of_with_injection l vl
                                                     (OITEnv_cons x (val_to_oitval (V_Couple v1' v2')) oitc_) e2 v2)) as [H_ex|H_nex].
  (*** e2 has a value *)
  clear H_not_exists.
  inversion_clear H_ex as [v2_ H_val_of_e2_].
  specialize (H_exists v2_ H_val_of_e2_).
  inversion_clear H_exists.
  assert(HH_val_of_in_e2:=val_of_with_injection_in_partially_approximated_oitenv 
                            (OITEnv_cons x (val_to_oitval (V_Couple v1 v2)) oitc)
                            (OITEnv_cons x (val_to_oitval (V_Couple v1' v2')) oitc_)
                            l vl e2 v2_).
  assert(HH:partially_approximated_oitenv
              (OITEnv_cons x (val_to_oitval (V_Couple v1 v2)) oitc)
              (OITEnv_cons x (val_to_oitval (V_Couple v1' v2')) oitc_)); auto_papprox.
  apply partially_approximated_val_to_oival; auto.
  apply partially_approximated_val_to_oival; auto.
  specialize (HH_val_of_in_e2 HH H_val_of_e2_).
  clear HH.
  inversion_clear HH_val_of_in_e2 as [vv2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v2].
  inversion_clear H_deps_spec.
  specialize (H3 vv2 H_val_of_e2).
  inversion_clear H3 as [H_tf' H_f'].
  rewrite H2, H_f'; auto_papprox.
  (*** e2 has no value *)
  clear H_exists.
  specialize (H_not_exists H_nex).
  inversion_clear H_not_exists as [H_tf'_ H_f'_].
  rewrite H_f'_; auto_papprox.

  (** p = Couple *)
  simpl in H_deps_spec; simpl in H_deps_spec_.
  inversion_clear H_deps_spec_ as [H_exists H_not_exists].
  destruct (excluded_middle (exists v1 : val,
                    val_of_with_injection l vl
                      (OITEnv_cons i (val_to_oitval v1')
                         (OITEnv_cons i0 (val_to_oitval v2') oitc_)) e1 v1)) as [H_ex|H_nex].
  (**** e1 has a value *)
  clear H_not_exists.
  inversion_clear H_ex as [v1_ H_val_of_e1_].
  specialize (H_exists v1_ H_val_of_e1_).
  inversion_clear H_exists.
  simpl in H_deps_spec; simpl in H_val_of_e1_.
  assert(HH_val_of_in_e1:=val_of_with_injection_in_partially_approximated_oitenv
                            (OITEnv_cons i (val_to_oitval v1) (OITEnv_cons i0 (val_to_oitval v2) oitc))
                            (OITEnv_cons i (val_to_oitval v1') (OITEnv_cons i0 (val_to_oitval v2') oitc_))
                            l vl e1 v1_).
  assert(HH:partially_approximated_oitenv (OITEnv_cons i (val_to_oitval v1) (OITEnv_cons i0 (val_to_oitval v2) oitc))
                                          (OITEnv_cons i (val_to_oitval v1') (OITEnv_cons i0 (val_to_oitval v2') oitc_))); auto_papprox.
  apply partially_approximated_val_to_oival; auto.
  apply partially_approximated_val_to_oival; auto.
  specialize (HH_val_of_in_e1 HH H_val_of_e1_).
  clear HH.
  inversion_clear HH_val_of_in_e1 as [vv1 HH].
  inversion_clear HH as [H_val_of_e1 H_papprox_v1].
  inversion_clear H_deps_spec.
  specialize (H3 vv1 H_val_of_e1).
  inversion_clear H3 as [H_tf' H_f'].
  rewrite H2, H_f'; auto_papprox.
  (**** e1 has no value *)
  clear H_exists.
  specialize (H_not_exists H_nex).
  inversion_clear H_not_exists as [H_tf'_ H_f'_].
  rewrite H_f'_; auto_papprox.
Qed.

Lemma deps_spec_Match_in_partially_approximated :
  forall (oitc oitc_:oitenv) (p:pattern) (x:identifier) (e1 e2:expr)
         (oid oid_ oid' oid'_:oideps) (oitd' oitd'_:oitdeps),
    deps_spec_Match oitc p x e1 e2 oid oitd' oid'
    -> deps_spec_Match oitc_ p x e1 e2 oid_ oitd'_ oid'_
    -> partially_approximated_oitenv oitc oitc_
    -> partially_approximated_oideps oid oid_
    -> partially_approximated_oitdeps oitd' oitd'_
       /\ partially_approximated_oideps oid' oid'_.
Proof.
  intros oitc oitc_ p x e1 e2 oid.
  revert oitc oitc_ e1 e2.
  
  induction oid;
  intros oitc oitc_ e1 e2 oid_ oid' oid'_ oitd' oitd'_ H_deps_spec_Match H_deps_spec_Match_ H_oitc_ H_oid_.

  (* case oid1 = nil *)
  inversion H_deps_spec_Match.
  inversion H_oid_.
  rewrite <-H7 in H_deps_spec_Match_.
  inversion H_deps_spec_Match_.
  split; auto_papprox.

  (* case oid1 = cons .. ... *)
  destruct a as [l f].
  inversion H_deps_spec_Match.
  inversion H_oid_.
  rewrite <-H13 in H_deps_spec_Match_.
  inversion H_deps_spec_Match_.
  specialize (IHoid _ _ _ _ _ _ _ _ _ H9 H27 H_oitc_ H15).
  inversion IHoid.
  split; auto_papprox.
  
  apply (deps_spec_Match_tf_in_partially_approximated oitc oitc_ p x e1 e2 l f f'0) with (f':=f') (f'_:=f'1); auto.
  apply (deps_spec_Match_f_in_partially_approximated oitc oitc_ p x e1 e2 l f f'0) with (tf':=tf') (tf'_:=tf'0); auto.
Qed.

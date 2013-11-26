Add Rec LoadPath "." as DEP_AI.


Require Import language.
Require Import values.
Require Import List.

Require Import instrumented_values.

Require Import abstract_values.

Fixpoint binders_of_pattern_aux (p:pattern) (acc:list identifier) : list identifier :=
  match p with
    | P_Constr0 n => acc
    | P_Constr1 n x => cons x acc
    | P_Couple x1 x2 => cons x1 (cons x2 acc)
  end.
      

Fixpoint deps_of_freevars_aux (e:expr) (ac:aenv) (bv:list identifier) (acc:adeps) : adeps :=
  match e with
    | Num n => nil
    | Constr0 n => nil
    | Constr1 n e => deps_of_freevars_aux e ac bv acc
    | Var x =>
      match assoc_ident_in_atenv x (aenv_to_atenv ac) with
        | Ident_not_in_atenv => nil (* ill-formed arguments e and ac *)
        | Ident_in_atenv (ATV _ (AV ad _)) => ad
      end
    | Lambda x e => deps_of_freevars_aux e ac (cons x bv) acc
    | Rec f x e => deps_of_freevars_aux e ac (cons f (cons x bv)) acc
    | Apply e1 e2 =>
      let acc := deps_of_freevars_aux e1 ac bv acc in
      deps_of_freevars_aux e2 ac bv acc
    | If e e1 e2 =>
      let acc := deps_of_freevars_aux e ac bv acc in
      let acc := deps_of_freevars_aux e1 ac bv acc in
      deps_of_freevars_aux e2 ac bv acc
    | Expr_match e (p,e1) None =>
      let acc := deps_of_freevars_aux e ac bv acc in
      deps_of_freevars_aux e1 ac (binders_of_pattern_aux p bv) acc
    | Expr_match e (p,e1) (Some (x,e2)) =>
      let acc := deps_of_freevars_aux e ac bv acc in
      let acc := deps_of_freevars_aux e1 ac (binders_of_pattern_aux p bv) acc in
      deps_of_freevars_aux e2 ac (cons x bv) acc
    | Couple e1 e2 =>
      let acc := deps_of_freevars_aux e1 ac bv acc in
      deps_of_freevars_aux e2 ac bv acc
    | Annot l e => deps_of_freevars_aux e ac bv acc
    | Let_in x e1 e2 =>
      let acc := deps_of_freevars_aux e1 ac (cons x bv) acc in
      deps_of_freevars_aux e2 ac bv acc
  end.

Definition deps_of_freevars (e:expr) (ac:aenv) : adeps :=
  deps_of_freevars_aux e ac nil nil.



Definition is_filtered_atval (atu:atval) (p:pattern) : filtered_atval_result :=
  match atu, p with
    | ATV _ (AV _ (AV_Constr0 n)), P_Constr0 n' =>
      if eq_nat_dec n n'
      then Filtered_atval_result_Match ATEnv_empty
      else Filtered_atval_result_Match_var
    | ATV _ (AV _ (AV_Constr0 _)), _ => Filtered_atval_result_Match_var

    | ATV _ (AV _ (AV_Constr1 n u)), P_Constr1 n' x =>
      if eq_nat_dec n n'
      then Filtered_atval_result_Match (ATEnv_cons x (ATV nil u) ATEnv_empty)
      else Filtered_atval_result_Match_var
    | ATV _ (AV _ (AV_Constr1 _ _)), _ => Filtered_atval_result_Match_var

    | ATV _ (AV _ (AV_Couple u1 u2)), P_Couple x1 x2 =>
      Filtered_atval_result_Match (ATEnv_cons x1 (ATV nil u1) (ATEnv_cons x2 (ATV nil u2) ATEnv_empty))
    | ATV _ (AV _ (AV_Couple _ _)), _ => Filtered_atval_result_Match_var

    | ATV _ (AV _ AV_Top), P_Constr0 _ =>
      Filtered_atval_result_Match_unknown ATEnv_empty
    | ATV _ (AV _ AV_Top), P_Constr1 _ x =>
      Filtered_atval_result_Match_unknown (ATEnv_cons x (ATV nil (AV nil AV_Top)) ATEnv_empty)
    | ATV _ (AV _ AV_Top), P_Couple x1 x2 =>
      Filtered_atval_result_Match_unknown (ATEnv_cons x1 (ATV nil (AV nil AV_Top))
                                                      (ATEnv_cons x2 (ATV nil (AV nil AV_Top)) ATEnv_empty))

    | _,_ => Filtered_atval_result_Error
  end.

      


Inductive atval_of : atenv -> expr -> atval -> Prop :=
| ATVal_of_Num :
  forall (v:Z) (atc:atenv),
    atval_of atc (Num v) (ATV nil (AV nil (AV_Top)))
| ATVal_of_Ident :
  forall (atc:atenv) (x:identifier) (atu:atval),
    assoc_ident_in_atenv x atc = Ident_in_atenv atu
    -> atval_of atc (Var x) atu
| ATVal_of_Lambda :
  forall (atc:atenv) (x:identifier) (e:expr) (atu:atval),
    atu = ATV nil (AV nil (AV_Closure x e (atenv_to_aenv atc)))
    -> atval_of atc (Lambda x e) atu
| ATVal_of_Rec :
  forall (atc:atenv) (f x:identifier) (e:expr) (atu:atval),
    atu = ATV nil (AV nil (AV_Rec_Closure f x e (atenv_to_aenv atc)))
    -> atval_of atc (Rec f x e) atu

| ATVal_of_Apply :
  forall (atc:atenv) (ac1:aenv) (e1 e2 e : expr) (x : identifier)
    (atu2 atu:atval) (au2:aval) (ad ad1:adeps) (atd1 atd2 atd:atdeps) (av:aval0),
(* construction de la valeur *)
    atval_of atc e1 (ATV atd1 (AV ad1 (AV_Closure x e ac1)))
    -> atval_of atc e2 atu2
    -> atu2 = ATV atd2 au2
    -> atval_of (ATEnv_cons x atu2 (aenv_to_atenv ac1)) e (ATV atd (AV ad av))
(* résultat de l'application *)
    -> atu = ATV (conc_atdeps atd1 (conc_atdeps atd2 (conc_atdeps atd ad1))) (AV (conc_adeps ad1 ad) av)
    -> atval_of atc (Apply e1 e2) atu

| ATVal_of_Apply_rec :
  forall (atc:atenv) (ac1:aenv) (e1 e2 e:expr) (f x:identifier)
    (atu2 atu atu_f:atval) (au2:aval) (ad ad1:adeps) (atd1 atd2 atd:atdeps) (av:aval0),
(* construction de la valeur *)
    atval_of atc e1 (ATV atd1 (AV ad1 (AV_Rec_Closure f x e ac1)))
    -> atu_f = ATV atd1 (AV (deps_of_freevars (Rec f x e) (atenv_to_aenv atc)) AV_Top)
    -> atval_of atc e2 atu2
    -> atu2 = ATV atd2 au2
    -> atval_of (ATEnv_cons f atu_f (ATEnv_cons x atu2 (aenv_to_atenv ac1))) e (ATV atd (AV ad av))
(* résultat de l'application *)
    -> atu = ATV (conc_atdeps atd1 (conc_atdeps atd2 (conc_atdeps atd ad1))) (AV (conc_adeps ad1 ad) av)
    -> atval_of atc (Apply e1 e2) atu

| ATVal_of_Apply_unknown :
  forall (atc:atenv) (e1 e2: expr)
    (atu:atval) (atd1 atd2:atdeps) (ad1 ad2:adeps) (av1 av2:aval0),
(* construction de la valeur *)
    atval_of atc e1 (ATV atd1 (AV ad1 av1))
    -> (match av1 with
            | AV_Closure _ _ _ => False
            | _ => True
        end)
    -> atval_of atc e2 (ATV atd2 (AV ad2 av2))
(* résultat de l'application *)
    -> atu = ATV (conc_atdeps atd1 (conc_atdeps atd2 (conc_atdeps ad1 ad2))) (AV (conc_adeps ad1 ad2) AV_Top)
    -> atval_of atc (Apply e1 e2) atu

(* TODO: for a more refine analysis, if the value of e1 or e2 is Bottom, return Bottom *)

| ATVal_of_Let_in :
  forall (atc:atenv) (x:identifier) (e1 e2:expr) (atu1 atu2:atval) (atd1 atd2:atdeps) (au1 au2:aval),
    atval_of atc e1 atu1
    -> atu1 = (ATV atd1 au1)
    -> atval_of (ATEnv_cons x atu1 atc) e2 atu2
    -> atu2 = (ATV atd2 au2)
    -> atval_of atc (Let_in x e1 e2) (ATV (conc_atdeps atd1 atd2) au2)

| ATVal_of_If :
  forall (atc:atenv) (e e1 e2:expr) (atd atd1 atd2:atdeps) (ad ad1 ad2:adeps) (atu1 atu2:atval) (av1 av2:aval0),
    atval_of atc e (ATV atd (AV ad (AV_Top)))
    -> atval_of atc e1 atu1
    -> atu1 = (ATV atd1 (AV ad1 av1))
    -> atval_of atc e2 atu2
    -> atu2 = (ATV atd2 (AV ad2 av2))
    -> atval_of atc (If e e1 e2) (ATV (conc_atdeps ad (conc_atdeps atd (conc_atdeps atd1 atd2)))
                                      (AV (conc_adeps ad (conc_adeps ad1 ad2)) AV_Top))

| ATVal_of_Match : 
  forall (atc atc_p:atenv) (e e1 e2: expr) (p:pattern) (x:identifier)
         (atu atu1:atval) (atd atd1:atdeps) (ad ad1:adeps) (av av1:aval0),
    atval_of atc e atu
    -> atu = (ATV atd (AV ad av))
    -> is_filtered_atval atu p = Filtered_atval_result_Match atc_p
    -> atval_of (conc_atenv atc_p atc) e1 atu1
    -> atu1 = (ATV atd1 (AV ad1 av1))
    -> atval_of atc (Expr_match e (p,e1) (Some (x,e2)))
                (ATV (conc_atdeps ad (conc_atdeps atd atd1))
                     (AV (conc_adeps ad ad1) av1))
(* TODO: il manque le cas de l'évaluation de (Expr_match e (p,e1) None), la match à une branche !!! *)

| ATVal_of_Match_var : 
  forall (atc atc_p:atenv) (e e1 e2: expr) (p:pattern) (x:identifier)
         (atu atu2:atval) (atd atd2:atdeps) (ad ad2:adeps) (av av2:aval0),
    atval_of atc e atu
    -> atu = (ATV atd (AV ad av))
    -> is_filtered_atval atu p = Filtered_atval_result_Match_var
    -> atval_of (ATEnv_cons x atu atc) e2 atu2
    -> atu2 = (ATV atd2 (AV ad2 av2))
    -> atval_of atc (Expr_match e (p,e1) (Some (x,e2)))
                (ATV (conc_atdeps ad (conc_atdeps atd atd2))
                     (AV (conc_adeps ad ad2) av2))

| ATVal_of_Match_unknown : 
  forall (atc atc_p:atenv) (e e1 e2: expr) (p:pattern) (x:identifier)
         (atu atu1 atu2:atval) (atd atd1 atd2:atdeps) (ad ad1 ad2:adeps) (av av1 av2:aval0),
    atval_of atc e atu
    -> atu = (ATV atd (AV ad av))
    -> is_filtered_atval atu p = Filtered_atval_result_Match_unknown atc_p
    -> atval_of (conc_atenv atc_p atc) e1 atu1
    -> atu1 = (ATV atd1 (AV ad1 av1))
    -> atval_of (ATEnv_cons x atu atc) e2 atu2
    -> atu2 = (ATV atd2 (AV ad2 av2))
    -> atval_of atc (Expr_match e (p,e1) (Some (x,e2)))
                (ATV (conc_atdeps ad (conc_atdeps atd (conc_atdeps atd1 atd2)))
                     (AV (conc_adeps ad (conc_adeps ad1 ad2)) AV_Top))

| ATVal_of_Match_bottom : 
  forall (atc atc_p:atenv) (e e1 e2: expr) (p:pattern) (x:identifier)
         (atu:atval) (atd:atdeps) (ad:adeps) (av:aval0),
    atval_of atc e atu
    -> atu = (ATV atd (AV ad av))
    -> is_filtered_atval atu p = Filtered_atval_result_Error
    -> atval_of atc (Expr_match e (p,e1) (Some (x,e2)))
                (ATV nil (AV nil AV_Bottom))

| ATVal_of_Constr0 :
  forall (atc:atenv) (n:constr),
    atval_of atc (Constr0 n) (ATV nil (AV nil (AV_Constr0 n)))

| ATVal_of_Constr1 :
  forall (atc:atenv) (n:constr) (e:expr) (atd:atdeps) (au:aval),
    atval_of atc e (ATV atd au)
    -> atval_of atc (Constr1 n e) (ATV atd (AV nil (AV_Constr1 n au)))

| ATVal_of_Couple :
  forall (atc:atenv) (e1 e2:expr) (atd1 atd2:atdeps) (au1 au2:aval),
    atval_of atc e1 (ATV atd1 au1)
    -> atval_of atc e2 (ATV atd2 au2)
    -> atval_of atc (Couple e1 e2) (ATV (conc_atdeps atd1 atd2) (AV nil (AV_Couple au1 au2)))
    
| ATVal_of_Annot :
  forall (atc:atenv) (l:label) (e:expr) (atd:atdeps) (ad:adeps) (av:aval0),
    atval_of atc e (ATV atd (AV ad av))
    -> atval_of atc (Annot l e) (ATV atd (AV (cons l ad) av))
.

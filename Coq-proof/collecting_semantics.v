
Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.
Require Import operational_semantics.

Require Import instrumented_values.
Require Import instrumented_semantics.

Require Import itval_val_conversion.
Require Import ctval_imval_conversion.

Require Import collecting_values.

Require Import ensembles.


Inductive filtered_ctval_result : Type :=
| Filtered_ctval_result_Match (c_p:ctenv)
| Filtered_ctval_result_Match_var
| Filtered_ctval_result_Match_unknown (c_p:ctenv)
| Filtered_ctval_result_Error.

Definition ivs_of_matchable : Ensemble ival0 :=
  fun iv => match iv with
              | IV_Constr0 _ => True
              | IV_Constr1 _ _ => True
              | IV_Couple _ _ => True
              | _ => False
            end.

Definition ivs_Constr0 (n:constr) : Ensemble ival0 :=
  fun iv => match iv with
              | IV_Constr0 n' => n = n'
              | _ => False
            end.

Definition ivs_Constr1 (n:constr) : Ensemble ival0 :=
  fun iv => match iv with
              | IV_Constr1 n' _ => n = n'
              | _ => False
            end.

Definition ivs_Couple : Ensemble ival0 :=
  fun iv => match iv with
              | IV_Couple _ _ => True
              | _ => False
            end.

(*
in is_filtered_ctval predicate, we assume that (Intersection _ ivs ivs_of_matchable) is not empty
*)
Inductive is_filtered_ctval : ctval -> pattern -> filtered_ctval_result -> Prop :=
| Is_filtered_ctval_Constr0 :
    forall (td:itdeps) (d:ideps) (ivs:Ensemble ival0) (n:constr),
      Included _ (Intersection _ ivs ivs_of_matchable) (ivs_Constr0 n)
      -> is_filtered_ctval (CTVal td d ivs) (P_Constr0 n)
                           (Filtered_ctval_result_Match CTEnv_empty)
| Is_filtered_ctval_Constr0_var :
    forall (td:itdeps) (d:ideps) (ivs:Ensemble ival0) (n:constr),
      not (Inhabited _ (Intersection _ ivs (ivs_Constr0 n)))
      -> is_filtered_ctval (CTVal td d ivs) (P_Constr0 n)
                           (Filtered_ctval_result_Match_var)
| Is_filtered_ctval_Constr0_unknown :
    forall (td:itdeps) (d:ideps) (ivs:Ensemble ival0) (n:constr),
      not (Included _ (Intersection _ ivs ivs_of_matchable) (ivs_Constr0 n))
      -> Inhabited _ (Intersection _ ivs (ivs_Constr0 n))
      -> is_filtered_ctval (CTVal td d ivs) (P_Constr0 n)
                           (Filtered_ctval_result_Match_unknown CTEnv_empty)

| Is_filtered_ctval_Constr1 :
    forall (td:itdeps) (d d':ideps) (ivs ivs':Ensemble ival0) (n:constr) (x:identifier),
      Included _ (Intersection _ ivs ivs_of_matchable) (ivs_Constr1 n)
      -> ivs' = SetMap (fun iv => match iv with
                                    | IV_Constr1 _ (IV_ _ iv') => iv'
                                    | _ => IV_Num 0 (* TODO: comment virer ou expliquer ça ??? *)
                                  end) ivs
      (* TODO: comment virer ou expliquer ça ???
         on devrait peut-être écrire :
         ivs' = (fun iv => exists (d:ideps), In _ ivs (IV_Constr1 n (IV_ d iv')))
         mais la version avec le SetMap est correcte puisqu'on a l'hypothèse (Included _ ivs (ivs_Constr1 n))
       *)
      -> d_of_imval (SetMap (fun iv => match iv with
                                         | IV_Constr1 _ iu => IV nil iu
                                         | _ => IV nil (IV_ nil (IV_Num 0)) (* TODO: comment virer ou expliquer ça ??? *)
                                       end) ivs) d'
      -> is_filtered_ctval (CTVal td d ivs) (P_Constr1 n x)
                           (Filtered_ctval_result_Match (CTEnv_cons x (CTVal nil d' ivs') CTEnv_empty))
| Is_filtered_ctval_Constr1_var :
    forall (td:itdeps) (d:ideps) (ivs:Ensemble ival0) (n:constr) (x:identifier),
      not (Inhabited _ (Intersection _ ivs (ivs_Constr1 n)))
      -> is_filtered_ctval (CTVal td d ivs) (P_Constr1 n x)
                           (Filtered_ctval_result_Match_var)
| Is_filtered_ctval_Constr1_unknown :
    forall (td:itdeps) (d d':ideps) (ivs ivs':Ensemble ival0) (n:constr) (x:identifier),
      not (Included _ (Intersection _ ivs ivs_of_matchable) (ivs_Constr1 n))
      -> Inhabited _ (Intersection _ ivs (ivs_Constr1 n))
      -> ivs' = SetMap (fun iv => match iv with
                                    | IV_Constr1 _ (IV_ _ iv') => iv'
                                    | _ => IV_Num 0 (* TODO: comment virer ou expliquer ça ??? *)
                                  end) (Intersection _ ivs (ivs_Constr1 n))
      -> d_of_imval (SetMap (fun iv => match iv with
                                         | IV_Constr1 _ iu => IV nil iu
                                         | _ => IV nil (IV_ nil (IV_Num 0)) (* TODO: comment virer ou expliquer ça ??? *)
                                       end) (Intersection _ ivs (ivs_Constr1 n))) d'
      -> is_filtered_ctval (CTVal td d ivs) (P_Constr1 n x)
                           (Filtered_ctval_result_Match_unknown (CTEnv_cons x (CTVal nil d' ivs') CTEnv_empty))

| Is_filtered_ctval_Couple :
    forall (td:itdeps) (d d1' d2':ideps) (ivs ivs1 ivs2:Ensemble ival0) (x1 x2:identifier),
      Included _ (Intersection _ ivs ivs_of_matchable) ivs_Couple
      -> ivs1 = SetMap (fun iv => match iv with
                                    | IV_Couple (IV_ _ iv1) _ => iv1
                                    | _ => IV_Num 0 (* TODO: comment virer ou expliquer ça ??? *)
                                  end) ivs
      -> ivs2 = SetMap (fun iv => match iv with
                                    | IV_Couple _ (IV_ _ iv2) => iv2
                                    | _ => IV_Num 0 (* TODO: comment virer ou expliquer ça ??? *)
                                  end) ivs
      -> d_of_imval (SetMap (fun iv => match iv with
                                         | IV_Couple iu1 _ => IV nil iu1
                                         | _ => IV nil (IV_ nil (IV_Num 0)) (* TODO: comment virer ou expliquer ça ??? *)
                                       end) ivs) d1'
      -> d_of_imval (SetMap (fun iv => match iv with
                                         | IV_Couple _ iu2 => IV nil iu2
                                         | _ => IV nil (IV_ nil (IV_Num 0)) (* TODO: comment virer ou expliquer ça ??? *)
                                       end) ivs) d2'
      -> is_filtered_ctval (CTVal td d ivs) (P_Couple x1 x2)
                           (Filtered_ctval_result_Match (CTEnv_cons x1 (CTVal nil d1' ivs1)
                                                                    (CTEnv_cons x2 (CTVal nil d2' ivs2)
                                                                                CTEnv_empty)))
| Is_filtered_ctval_Couple_var :
    forall (td:itdeps) (d:ideps) (ivs:Ensemble ival0) (x1 x2:identifier),
      not (Inhabited _ (Intersection _ ivs ivs_Couple))
      -> is_filtered_ctval (CTVal td d ivs) (P_Couple x1 x2)
                           (Filtered_ctval_result_Match_var)
| Is_filtered_ctval_Couple_unknown :
    forall (td:itdeps) (d d1' d2':ideps) (ivs ivs1 ivs2:Ensemble ival0) (x1 x2:identifier),
      not (Included _ (Intersection _ ivs ivs_of_matchable) ivs_Couple)
      -> (Inhabited _ (Intersection _ ivs ivs_Couple))
      -> ivs1 = SetMap (fun iv => match iv with
                                    | IV_Couple (IV_ _ iv1) _ => iv1
                                    | _ => IV_Num 0 (* TODO: comment virer ou expliquer ça ??? *)
                                  end) (Intersection _ ivs ivs_Couple)
      -> ivs2 = SetMap (fun iv => match iv with
                                    | IV_Couple _ (IV_ _ iv2) => iv2
                                    | _ => IV_Num 0 (* TODO: comment virer ou expliquer ça ??? *)
                                  end) (Intersection _ ivs ivs_Couple)
      -> d_of_imval (SetMap (fun iv => match iv with
                                         | IV_Couple iu1 _ => IV nil iu1
                                         | _ => IV nil (IV_ nil (IV_Num 0)) (* TODO: comment virer ou expliquer ça ??? *)
                                       end) (Intersection _ ivs ivs_Couple)) d1'
      -> d_of_imval (SetMap (fun iv => match iv with
                                         | IV_Couple _ iu2 => IV nil iu2
                                         | _ => IV nil (IV_ nil (IV_Num 0)) (* TODO: comment virer ou expliquer ça ??? *)
                                       end) (Intersection _ ivs ivs_Couple)) d2'
      -> is_filtered_ctval (CTVal td d ivs) (P_Couple x1 x2)
                           (Filtered_ctval_result_Match_unknown (CTEnv_cons x1 (CTVal nil d1' ivs1)
                                                                            (CTEnv_cons x2 (CTVal nil d2' ivs2)
                                                                                        CTEnv_empty)))
.

Inductive ident_in_ctenv : Type :=
  | Ident_not_in_ctenv : ident_in_ctenv
  | Ident_in_ctenv : ctval -> ident_in_ctenv.

Fixpoint assoc_ident_in_ctenv (x:identifier) (ctc:ctenv) {struct ctc} :
 ident_in_ctenv :=
match ctc with
| CTEnv_empty => Ident_not_in_ctenv
| CTEnv_cons x' u c' =>
  if (beq_identifier x x')
  then (Ident_in_ctenv u)
  else (assoc_ident_in_ctenv x c')
end.

Fixpoint conc_ctenv c c' :=
  match c with
    | CTEnv_empty => c'
    | CTEnv_cons x v c'' => CTEnv_cons x v (conc_ctenv c'' c')
  end.

Definition ival_to_ctval (iu:ival) : ctval :=
  match iu with
    | IV_ d v => CTVal nil d (Singleton _ v)
  end.

Fixpoint ienv_to_ctenv (ic:ienv) : ctenv :=
  match ic with
    | IEnv_empty => CTEnv_empty
    | IEnv_cons x iu ic' =>
      CTEnv_cons x (ival_to_ctval iu) (ienv_to_ctenv ic')
  end.


Inductive BigUnion {U:Type} (AA:Ensemble (Ensemble U)) : Ensemble U :=
| BigUnion_intro :
    forall (A:Ensemble U) (a:U),
      In _ AA A
      -> In _ (A) a
      -> In _ (BigUnion AA) a.
   

Inductive ctval_of : ctenv -> expr -> ctval -> Prop :=
| CTVal_of_Num :
  forall (ctc:ctenv) (v:Z),
    ctval_of ctc (Num v) (CTVal nil nil (Singleton _ (IV_Num v)))

| CTVal_of_Constr0 :
  forall (ctc:ctenv) (n:constr),
    ctval_of ctc (Constr0 n) (CTVal nil nil (Singleton _ (IV_Constr0 n)))

| CTVal_of_Constr1 :
  forall (ctc:ctenv) (n:constr) (e:expr) (td:itdeps) (d:ideps) (ivs ivs':Ensemble ival0),
    ctval_of ctc e (CTVal td d ivs)
    -> ivs' = SetMap (fun iv => IV_Constr1 n (IV_ d iv)) ivs
    -> ctval_of ctc (Constr1 n e) (CTVal td nil ivs')

| CTVal_of_Ident :
    forall (ctc:ctenv) (x:identifier) (ctv:ctval),
      assoc_ident_in_ctenv x ctc = Ident_in_ctenv ctv
      -> ctval_of ctc (Var x) ctv

| CTVal_of_Ident_empty :
    forall (ctc:ctenv) (x:identifier),
      assoc_ident_in_ctenv x ctc = Ident_not_in_ctenv
      -> ctval_of ctc (Var x) (CTVal nil nil (Empty_set _))

| CTVal_of_Lambda :
    forall (ctc:ctenv) (x:identifier) (e:expr) (ctv:ctval) (ivs:Ensemble ival0),
    ivs = SetMap (fun itc => IV_Closure x e (itenv_to_ienv itc)) (ctenv_to_imenv ctc)
    -> ctval_of ctc (Lambda x e) (CTVal nil nil ivs)

| CTVal_of_Rec :
    forall (ctc:ctenv) (f x:identifier) (e:expr) (ctv:ctval) (ivs:Ensemble ival0),
    ivs = SetMap (fun itc => IV_Rec_Closure f x e (itenv_to_ienv itc)) (ctenv_to_imenv ctc)
    -> ctval_of ctc (Rec f x e) (CTVal nil nil ivs)

| CTVal_of_Apply :
    forall (ctc:ctenv) (e1 e2:expr)
           (td1 td2 td:itdeps) (d1 d2 d:ideps) (ivs1 ivs2:Ensemble ival0)
           (ctv:ctval)
           (imv:Ensemble itval),
    ctval_of ctc e1 (CTVal td1 d1 ivs1)
    -> ctval_of ctc e2 (CTVal td2 d2 ivs2)
    -> imv = (fun itu => (exists x e ic1 iv2 itd id iv,
                            In _ ivs1 (IV_Closure x e ic1)
                            /\ In _ ivs2 iv2
                            /\ ival_of (ITEnv_cons x (IV td2 (IV_ d2 iv2)) (ienv_to_itenv ic1))
                                       e
                                       (IV itd (IV_ id iv))
                            /\ itu = IV (conc_itdeps td1 (conc_itdeps td2 (conc_itdeps itd d1)))
                                        (IV_ (conc_ideps d1 id) iv))
                         \/ (exists f x e ic iv2 itd id iv,
                               In _ ivs1 (IV_Rec_Closure f x e ic)
                               /\ In _ ivs2 iv2
                               /\ ival_of (ITEnv_cons f (IV td1 (IV_ d1 (IV_Rec_Closure f x e ic)))
                                                      (ITEnv_cons x (IV td2 (IV_ d2 iv2)) (ienv_to_itenv ic)))
                                          e
                                          (IV itd (IV_ id iv))
                               /\ itu = IV (conc_itdeps td1 (conc_itdeps td2 (conc_itdeps itd d1)))
                                           (IV_ (conc_ideps d1 id) iv)))
    -> (forall l:label, List.In l td
                        <-> (exists td',
                               List.In l td'
                               /\ In _ (SetMap (fun itu => match itu with | IV td (IV_ d iv) => td end) imv) td'))
    -> (forall l:label, List.In l d
                        <-> (exists d',
                               List.In l d'
                               /\ In _ (SetMap (fun itu => match itu with | IV td (IV_ d iv) => d end) imv) d'))
    -> ctv = CTVal td
                   d
                   (SetMap (fun itu => match itu with | IV td (IV_ d iv) => iv end) imv)
    -> ctval_of ctc (Apply e1 e2) ctv

| CTVal_of_If_true :
    forall (ctc:ctenv) (e e1 e2:expr)
           (td td1:itdeps) (d d1:ideps) (ivs ivs1:Ensemble ival0),
      ctval_of ctc e (CTVal td d ivs)
      -> In _ ivs (IV_Bool true)
      -> (not (In _ ivs (IV_Bool false)))
      -> ctval_of ctc e1 (CTVal td1 d1 ivs1)
      -> ctval_of ctc (If e e1 e2) (CTVal (conc_itdeps d (conc_itdeps td td1))
                                          (conc_ideps d d1)
                                          ivs1)

| CTVal_of_If_false :
    forall (ctc:ctenv) (e e1 e2:expr)
           (td td2:itdeps) (d d2:ideps) (ivs ivs2:Ensemble ival0),
      ctval_of ctc e (CTVal td d ivs)
      -> Same_set _ ivs (Singleton _ (IV_Bool false))
      -> In _ ivs (IV_Bool false)
      -> (not (In _ ivs (IV_Bool true)))
      -> ctval_of ctc e2 (CTVal td2 d2 ivs2)
      -> ctval_of ctc (If e e1 e2) (CTVal (conc_itdeps d (conc_itdeps td td2))
                                          (conc_ideps d d2)
                                          ivs2)

| CTVal_of_If_unknown :
    forall (ctc:ctenv) (e e1 e2:expr)
           (td td1 td2:itdeps) (d d1 d2:ideps) (ivs ivs1 ivs2:Ensemble ival0),
      ctval_of ctc e (CTVal td d ivs)
      -> Included _ (Couple _ (IV_Bool true) (IV_Bool false)) ivs
      -> ctval_of ctc e1 (CTVal td1 d1 ivs1)
      -> ctval_of ctc e2 (CTVal td2 d2 ivs2)
      -> ctval_of ctc (If e e1 e2) (CTVal (conc_itdeps d (conc_itdeps td (conc_itdeps td1 td2)))
                                          (conc_ideps d (conc_ideps d1 d2))
                                          (Union _ ivs1 ivs2))

| CTVal_of_If_empty :
    forall (ctc:ctenv) (e e1 e2:expr)
           (td td1:itdeps) (d d1:ideps) (ivs ivs1:Ensemble ival0),
      ctval_of ctc e (CTVal td d ivs)
      -> (not (In _ ivs (IV_Bool true)))
      -> (not (In _ ivs (IV_Bool false)))
      -> ctval_of ctc (If e e1 e2) (CTVal nil nil (Empty_set _))

                  
| CTVal_of_Match :
    forall (ctv:ctval) (ctc ctc_p:ctenv) (e e1:expr)
           (br2:option (identifier*expr)) (p:pattern)
           (td td1:itdeps) (d d1:ideps) (ivs ivs1:Ensemble ival0),
      ctval_of ctc e ctv
      -> ctv = (CTVal td d ivs)
      -> Inhabited _ (Intersection _ ivs ivs_of_matchable)
      -> is_filtered_ctval ctv p (Filtered_ctval_result_Match ctc_p)
      -> ctval_of (conc_ctenv ctc_p ctc) e1 (CTVal td1 d1 ivs1)
      -> ctval_of ctc (Expr_match e (p,e1) br2) (CTVal (conc_itdeps d (conc_itdeps td td1))
                                                       (conc_ideps d d1)
                                                       ivs1)
    
| CTVal_of_Match_var :
    forall (ctv:ctval) (ctc:ctenv) (e e1 e2:expr)
           (p:pattern) (x:identifier)
           (td td2:itdeps) (d d2:ideps) (ivs ivs2:Ensemble ival0),
      ctval_of ctc e ctv
      -> ctv = (CTVal td d ivs)
      -> Inhabited _ (Intersection _ ivs ivs_of_matchable)
      -> is_filtered_ctval ctv p Filtered_ctval_result_Match_var
      -> ctval_of (CTEnv_cons x ctv ctc) e2 (CTVal td2 d2 ivs2)
      -> ctval_of ctc (Expr_match e (p,e1) (Some (x,e2))) (CTVal (conc_itdeps d (conc_itdeps td td2))
                                                                 (conc_ideps d d2)
                                                                 ivs2)
                  
| CTVal_of_Match_unknown :
    forall (ctv:ctval) (ctc ctc_p:ctenv) (e e1 e2:expr)
           (p:pattern) (x:identifier)
           (td td1 td2:itdeps) (d d1 d2:ideps) (ivs ivs1 ivs2:Ensemble ival0),
      ctval_of ctc e ctv
      -> ctv = (CTVal td d ivs)
      -> Inhabited _ (Intersection _ ivs ivs_of_matchable)
      -> is_filtered_ctval ctv p (Filtered_ctval_result_Match_unknown ctc_p)
      -> ctval_of (conc_ctenv ctc_p ctc) e1 (CTVal td1 d1 ivs1)
      -> ctval_of (CTEnv_cons x ctv ctc) e2 (CTVal td2 d2 ivs2)
      -> ctval_of ctc (Expr_match e (p,e1) (Some (x,e2))) (CTVal (conc_itdeps d (conc_itdeps td (conc_itdeps td1 td2)))
                                                                 (conc_ideps d (conc_ideps d1 d2))
                                                                 (Union _ ivs1 ivs2))

| CTVal_of_Match_empty :
    forall (ctv:ctval) (ctc ctc_p:ctenv) (e e1:expr)
           (br2:option (identifier*expr)) (p:pattern)
           (td td1:itdeps) (d d1:ideps) (ivs ivs1:Ensemble ival0),
      ctval_of ctc e ctv
      -> ctv = (CTVal td d ivs)
      -> not (Inhabited _ (Intersection _ ivs ivs_of_matchable))
      -> ctval_of ctc (Expr_match e (p,e1) br2) (CTVal nil nil (Empty_set _))
    
| CTVal_of_Couple :
  forall (ctc:ctenv) (e1 e2:expr) (td1 td2:itdeps) (d1 d2:ideps) (ivs1 ivs2 ivs':Ensemble ival0),
    ctval_of ctc e1 (CTVal td1 d1 ivs1)
    -> ctval_of ctc e2 (CTVal td2 d2 ivs2)
    -> ivs' = SetMap2 (fun iv1 iv2 => IV_Couple (IV_ d1 iv1) (IV_ d2 iv2)) ivs1 ivs2
    -> ctval_of ctc (language.Couple e1 e2) (CTVal (conc_itdeps td1 td2) nil ivs')

| CTVal_of_Annot :
  forall (ctc:ctenv) (l:label) (e:expr) (td:itdeps) (d:ideps) (ivs:Ensemble ival0),
    ctval_of ctc e (CTVal td d ivs)
    -> ctval_of ctc (Annot l e) (CTVal td (cons l d) ivs)

| CTVal_of_Let_in :
  forall (ctc:ctenv) (x:identifier) (e1 e2:expr)
         (ctv1 ctv2:ctval) (td1 td2:itdeps) (d1 d2:ideps) (ivs1 ivs2:Ensemble ival0),
    ctval_of ctc e1 ctv1
    -> ctv1 = (CTVal td1 d1 ivs1)
    -> (exists (iv1:ival0), In _ ivs1 iv1)
    -> ctval_of (CTEnv_cons x ctv1 ctc) e2 ctv2
    -> ctv2 = (CTVal td2 d2 ivs2)
    -> ctval_of ctc (Let_in x e1 e2) (CTVal (conc_itdeps td1 td2) d2 ivs2)
       
| CTVal_of_Let_in_empty :
  forall (ctc:ctenv) (x:identifier) (e1 e2:expr)
         (ctv1:ctval) (td1:itdeps) (d1:ideps) (ivs1:Ensemble ival0),
    ctval_of ctc e1 ctv1
    -> ctv1 = (CTVal td1 d1 ivs1)
    -> not (Inhabited _ ivs1)
    -> ctval_of ctc (Let_in x e1 e2) (CTVal nil nil (Empty_set _))
.

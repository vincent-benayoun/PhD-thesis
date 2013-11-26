Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.
Require Import over_instrumented_values.


(*----- APPLICATION OF IMPACT FUNCTIONS (oitdeps and oideps) -----*)

Fixpoint apply_impact_fun (l:label) (vl:val) (d:oideps) {struct d} : option val :=
  match d with
    | nil =>
      None
    | cons (l', f) tl =>
      if eq_label_dec l l'
        then Some (f vl)
        else apply_impact_fun l vl tl
  end.

Fixpoint apply_timpact_fun (l:label) (vl:val) (td:oitdeps) {struct td} : option bool :=
  match td with
    | nil =>
      None (* label l does not appear in td *)
    | cons (l', f) tl =>
      if eq_label_dec l l'
        then
          match apply_timpact_fun l vl tl with
            | Some b => (* label l appears several times in td *)
              Some (f vl || b)%bool
            | None => (* label l appears only once in td *)
              Some (f vl)
          end
        else (* label l<>l' appears or not in the tail of td *)
          apply_timpact_fun l vl tl
  end.


(*----- INSTANTIATION -----*)


Fixpoint instantiate_oival (l:label) (vl:val) (u:oival) {struct u} : option val :=
  match u with
    | OIV_ d oiv =>
      match apply_impact_fun l vl d with
        | None => instantiate_oival0 l vl oiv
        | Some v => Some v
      end
  end

with instantiate_oival0 (l:label) (vl:val) (oiv:oival0) {struct oiv} : option val :=
  match oiv with
    | OIV_Num n => Some (V_Num n)
    | OIV_Bool b => Some (V_Bool b)
    | OIV_Constr0 n => Some (V_Constr0 n)
    | OIV_Constr1 n u =>
      option_map (fun v => V_Constr1 n v) (instantiate_oival l vl u)
    | OIV_Closure x e c =>
      option_map (fun c => V_Closure x e c) (instantiate_oienv l vl c)
    | OIV_Couple u1 u2 =>
      option_map2 (fun v1 v2 => V_Couple v1 v2) (instantiate_oival l vl u1) (instantiate_oival l vl u2)
    | OIV_Rec_Closure f x e c =>
      option_map (fun c => V_Rec_Closure f x e c) (instantiate_oienv l vl c)
  end

with instantiate_oienv (l:label) (vl:val) (c:oienv) {struct c} : option env :=
  match c with
    | OIEnv_empty =>
      Some Env_empty
    | OIEnv_cons x u c' =>
      option_map2 (fun v c => Env_cons x v c) (instantiate_oival l vl u) (instantiate_oienv l vl c')
  end.


Definition instantiate_oitval (l:label) (vl:val) (uu:oitval) : option val :=
  match uu with
    | OIV td u =>
      match apply_timpact_fun l vl td with
        | Some true => None
        | _ => instantiate_oival l vl u
      end
  end.

Fixpoint instantiate_oitenv (l:label) (vl:val) (c:oitenv) {struct c} : option env :=
  match c with
    | OITEnv_empty =>
      Some Env_empty
    | OITEnv_cons x uu c' =>
      option_map2 (fun v c => Env_cons x v c) (instantiate_oitval l vl uu) (instantiate_oitenv l vl c')
  end.


(*----- LEMMAS -----*)


Lemma instantiable_oitenv :
  forall (l:label) (vl:val) (c:oitenv) (c':env),
    Some c' = instantiate_oitenv l vl c
    -> forall (i:identifier) (uu:oitval),
      assoc_ident_in_oitenv i c = Ident_in_oitenv uu
      -> exists (v:val), Some v = instantiate_oitval l vl uu.
Proof.
  induction c; simpl.

  intros c' H i uu H0.
  inversion H0.

  intros c' H i uu0 H0.
  unfold option_map2 in H.
  assert(H_SUM : {instantiate_oitval l vl uu = None} + {exists x, instantiate_oitval l vl uu = Some x});
    [induction (instantiate_oitval l vl uu); [right; exists a; reflexivity| left; reflexivity]
      | inversion H_SUM as [H_SUM1|H_SUM2]; [rewrite H_SUM1 in H; inversion H|inversion H_SUM2 as [u_inst H_SUM3_oival]; rewrite H_SUM3_oival in H; inversion H]];
    clear H_SUM H_SUM2 H2.
  induction (beq_identifier i x).

  exists u_inst.
  inversion H0 as [HH]; symmetry in HH; rewrite HH.
  symmetry; assumption.

  assert(H_SUM : {instantiate_oitenv l vl c = None} + {exists x, instantiate_oitenv l vl c = Some x});
    [induction (instantiate_oitenv l vl c); [right; exists a; reflexivity| left; reflexivity]
      | inversion H_SUM as [H_SUM1|H_SUM2]; [rewrite H_SUM1 in H; inversion H|inversion H_SUM2 as [c_inst H_SUM3_oitenv]; rewrite H_SUM3_oitenv in H; inversion H as [HHHH]]];
    clear H_SUM H_SUM2.

  apply IHc with (c':=c_inst) (i:=i).
  symmetry; assumption.
  assumption.
Qed.


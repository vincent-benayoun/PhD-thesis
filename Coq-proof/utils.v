
Require Bool.

Lemma match_option_bool_not_true :
  forall (A:Type) (e:option bool) (e1 e2:A),
  e <> Some true
  -> match e with
       | Some true => e1
       | Some false => e2
       | None => e2
     end
     = e2.
Proof.
  intros A e e1 e2 H.
  induction e.
  induction a.
  elim H; reflexivity.
  reflexivity.
  reflexivity.
Qed.


Lemma match_option_bool_not_true2 :
  forall (o:option bool) (b0:bool),
    o <> Some true
    -> match o with
         | Some b => Some (b0 || b)%bool
         | None => Some (b0)
       end = Some b0.
Proof.
  intros o b0 H.
  destruct o; auto.
  destruct b.
  elim (H eq_refl).
  rewrite Bool.orb_false_r; auto.
Qed.



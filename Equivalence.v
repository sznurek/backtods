Require Import Terms.

Fixpoint rename_v (v:var) (r:Croot) : Croot :=
match r with
| Croot_exp e => Croot_exp (rename_exp_v v e)
end
with rename_exp_v (v:var) (e:Cexp) : Cexp :=
match e with
| Cexp_cont t          => Cexp_cont (rename_triv_v v t)
| Cexp_app t0 t1 v' e' => let t0' := rename_triv_v v t0 in
                          let t1' := rename_triv_v v t1 in
                          Cexp_app t0' t1' v (rename_exp_v v e')
end
with rename_triv_v (v:var) (t:Ctriv) : Ctriv :=
match t with
| Ctriv_var x   => Ctriv_var x
| Ctriv_lam x r => Ctriv_lam x (rename_v v r)
| Ctriv_vvar _  => Ctriv_vvar v
end.

Definition a_eq (r1:Croot) (r2:Croot) := rename_v 0 r1 = rename_v 0 r2.
Definition a_exp_eq (e1:Cexp) (e2:Cexp) := rename_exp_v 0 e1 = rename_exp_v 0 e2.
Definition a_triv_eq (t1:Ctriv) (t2:Ctriv) :=
  rename_triv_v 0 t1 = rename_triv_v 0 t2.

Lemma rename_exp_v_inv :
  forall (v v':var) (e:Cexp), rename_exp_v v (rename_exp_v v' e) = rename_exp_v v e.
Proof.
intros v v'.
apply (Cexp_mut (fun r => rename_v v (rename_v v' r) = rename_v v r)
                (fun t => rename_triv_v v (rename_triv_v v' t) = rename_triv_v v t)
                (fun e => rename_exp_v v (rename_exp_v v' e) = rename_exp_v v e));
intros; simpl; eauto.
rewrite H; auto.
rewrite H; auto.
rewrite H; auto.
rewrite H; rewrite H0; rewrite H1; auto.
Qed.

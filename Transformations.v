Require Import Terms.

Fixpoint cps_transform (r:Droot) : Croot :=
match r with
| Droot_exp e => Croot_exp (cps_exp_transform 0 e (fun _ t => Cexp_cont t))
end
with cps_exp_transform (f:var) (e:Dexp) (k:Cont) : Cexp :=
match e with
| Dexp_app e0 e1 => cps_exp_transform (S f) e0 (fun f0 t0 =>
                    cps_exp_transform f0 e1 (fun f1 t1 =>
                        Cexp_app t0 t1 f1 (k (S f1) (Ctriv_vvar f1))))
| Dexp_triv t    => k f (cps_triv_transform t)
end
with cps_triv_transform (t:Dtriv) : Ctriv :=
match t with
| Dtriv_var x   => Ctriv_var x
| Dtriv_lam x r => Ctriv_lam x (cps_transform r)
end.

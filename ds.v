Require Import List.
Require Import Arith.Plus.
Require Import ZArith.
Require Import FunctionalExtensionality.

Definition var := nat.

Inductive Croot : Set :=
| Croot_exp : Cexp -> Croot
with Cexp : Set :=
| Cexp_cont : Ctriv -> Cexp
| Cexp_app  : Ctriv -> Ctriv -> var -> Cexp -> Cexp
with Ctriv : Set :=
| Ctriv_var : var -> Ctriv
| Ctriv_vvar : var -> Ctriv
| Ctriv_lam : var -> Croot -> Ctriv.

Coercion Croot_exp : Cexp >-> Croot.
Coercion Ctriv_var : var >-> Ctriv.

Inductive CrootValid : Croot -> Prop :=
| CrootValid_exp : forall e:Cexp, CexpValid e nil -> CrootValid e
with CexpValid : Cexp -> list var -> Prop :=
| CexpValid_cont : forall (ksi:list var) (t:Ctriv), CtrivValid t ksi nil -> CexpValid (Cexp_cont t) ksi
| CexpValid_app  : forall (ksi0 ksi1 ksi2:list var) (v:var) (t0 t1:Ctriv) (e:Cexp),
                     CtrivValid t1 ksi0 ksi1 -> CtrivValid t0 ksi1 ksi2 ->
                     CexpValid e (v::ksi2) ->
                     CexpValid (Cexp_app t0 t1 v e) ksi0
with CtrivValid : Ctriv -> list var -> list var -> Prop :=
| CtrivValid_vvar : forall (ksi:list var) (v:var), CtrivValid (Ctriv_vvar v) (v::ksi) ksi
| CtrivValid_var  : forall (ksi:list var) (x:var), CtrivValid (Ctriv_var x) ksi ksi
| CtrivValid_lam  : forall (ksi:list var) (x:var) (r:Croot), CrootValid r -> CtrivValid (Ctriv_lam x r) ksi ksi.

Scheme Croot_mut := Induction for Croot Sort Type
with Ctriv_mut := Induction for Ctriv Sort Type
with Cexp_mut := Induction for Cexp Sort Type.

Scheme CrootValid_mut := Induction for CrootValid Sort Prop
with CtrivValid_mut := Induction for CtrivValid Sort Prop
with CexpValid_mut := Induction for CexpValid Sort Prop.

Hint Constructors Ctriv Cexp Croot.
Hint Constructors CtrivValid CexpValid CrootValid.

Inductive Droot : Set :=
| Droot_exp : Dexp -> Droot
with Dexp : Set :=
| Dexp_app  : Dexp -> Dexp -> Dexp
| Dexp_triv : Dtriv -> Dexp
with Dtriv : Set :=
| Dtriv_var : var -> Dtriv
| Dtriv_lam : var -> Droot -> Dtriv.

Coercion Droot_exp : Dexp >-> Droot.
Coercion Dexp_triv : Dtriv >-> Dexp.
Coercion Dtriv_var : var >-> Dtriv.

Scheme Droot_mut := Induction for Droot Sort Type
with Dexp_mut := Induction for Dexp Sort Type
with Dtriv_mut := Induction for Dtriv Sort Type.

Hint Constructors Droot Dexp Dtriv.

Definition Cont := (var -> Ctriv -> Cexp).

Fixpoint cps_transform (r:Droot) : Croot :=
match r with
| Droot_exp e => cps_exp_transform e 0 (fun _ t => Cexp_cont t)
end
with cps_exp_transform (e:Dexp) (f:var) (k:Cont) : Cexp :=
match e with
| Dexp_app e0 e1 => cps_exp_transform e0 f  (fun n0 t0 =>
                    cps_exp_transform e1 n0 (fun n1 t1 =>
                        Cexp_app t0 t1 n1 (k (S n1) (Ctriv_vvar n1))))
| Dexp_triv t    => k f (cps_triv_transform t)
end
with cps_triv_transform (t:Dtriv) : Ctriv :=
match t with
| Dtriv_var x   => x
| Dtriv_lam x r => Ctriv_lam x (cps_transform r)
end.

Definition good_continuation (k:Cont) (s:list var) :=
  forall (v:var) (t:Ctriv) (s':list var),
    CtrivValid t s' s -> CexpValid (k v t) s'.

Hint Unfold good_continuation.

Theorem cps_transform_valid :
  forall r:Droot, CrootValid (cps_transform r).
Proof.
apply (Droot_mut (fun r => CrootValid (cps_transform r))
                 (fun e => forall (v:var) (k:Cont) (s:list var),
                             good_continuation k s ->
                             CexpValid (cps_exp_transform e v k) s)
                 (fun t => forall (s:list var), CtrivValid (cps_triv_transform t) s s));
intros; unfold good_continuation in *; eauto; simpl; intuition; eauto.
Qed.

Inductive DsifyRoot : Croot -> Droot -> Prop :=
| DsifyRoot_exp : forall (e:Cexp) (e':Dexp), DsifyExp nil e e' -> DsifyRoot (Croot_exp e) (Droot_exp e')
with DsifyExp : list Dexp -> Cexp -> Dexp -> Prop :=
| DsifyExpTriv : forall (l:list Dexp) (t:Ctriv) (t':Dtriv),
                   DsifyTriv l nil t t' ->
                   DsifyExp l (Cexp_cont t) (Dexp_triv t')
| DsifyExpApp : forall (l l0 l1:list Dexp) (t0 t1:Ctriv) (e:Cexp) (v:var)
                       (t0' t1' e':Dexp),
                  DsifyTriv l l1 t1 t1' ->
                  DsifyTriv l1 l0 t0 t0' ->
                  DsifyExp (Dexp_app t0' t1' :: l0) e e' ->
                  DsifyExp l (Cexp_app t0 t1 v e) e'
with DsifyTriv : list Dexp -> list Dexp -> Ctriv -> Dexp -> Prop :=
| DsifyTrivVar : forall (x:var) (l:list Dexp), DsifyTriv l l (Ctriv_var x) (Dexp_triv (Dtriv_var x))
| DsifyTrivLam : forall (x:var) (r:Croot) (r':Droot) (l:list Dexp),
                   DsifyRoot r r' -> DsifyTriv l l (Ctriv_lam x r) (Dexp_triv (Dtriv_lam x r'))
| DsifyTrivVvar : forall (v:var) (e:Dexp) (l:list Dexp),
                    DsifyTriv (e::l) l (Ctriv_vvar v) e.

Scheme DsifyRoot_mut := Induction for DsifyRoot Sort Prop
with DsifyExp_mut := Induction for DsifyExp Sort Prop
with DsifyTriv_mut := Induction for DsifyTriv Sort Prop.

Theorem dsify_valid :
  forall (r:Croot), CrootValid r -> forall (r':Droot), DsifyRoot r r' -> cps_transform r' = r.
Proof.
apply (CrootValid_mut (fun r rv => forall (r':Droot), DsifyRoot r r' -> cps_transform r' = r)
                      (fun t l0 l1 tv => True)
                      (fun e l ev => True)).
Focus 6.
intros.


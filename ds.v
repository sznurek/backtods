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

Fixpoint cps_transform (r:Droot) : Croot :=
match r with
| Droot_exp e => cps_exp_transform e (fun t => Cexp_cont t)
end
with cps_exp_transform (e:Dexp) (k:Ctriv -> Cexp) : Cexp :=
match e with
| Dexp_app e0 e1 => cps_exp_transform e0 (fun t0 =>
                    cps_exp_transform e1 (fun t1 =>
                        Cexp_app t0 t1 0 (k (Ctriv_vvar 0))))
| Dexp_triv t    => k (cps_triv_transform t)
end
with cps_triv_transform (t:Dtriv) : Ctriv :=
match t with
| Dtriv_var x   => x
| Dtriv_lam x r => Ctriv_lam x (cps_transform r)
end.

Definition good_continuation (k:Ctriv -> Cexp) (s:list var) :=
  forall (t:Ctriv) (s':list var), CtrivValid t s' s -> CexpValid (k t) s'.

Hint Unfold good_continuation.

Theorem cps_transform_valid :
  forall r:Droot, CrootValid (cps_transform r).
Proof.
apply (Droot_mut (fun r => CrootValid (cps_transform r))
                 (fun e => forall (k:Ctriv -> Cexp) (s:list var),
                             good_continuation k s ->
                             CexpValid (cps_exp_transform e k) s)
                 (fun t => forall (s:list var), CtrivValid (cps_triv_transform t) s s));
intros; unfold good_continuation in *; eauto; simpl; intuition; eauto.
Qed.

Inductive DHroot : Set :=
| DHroot_exp : DHexp -> DHroot
with DHexp : Set :=
| DHexp_app  : DHexp -> DHexp -> DHexp
| DHexp_triv : DHtriv -> DHexp
with DHtriv : Set :=
| DHtriv_var  : var -> DHtriv
| DHtriv_lam  : var -> DHroot -> DHtriv
| DHtriv_vvar : var -> DHtriv.

Scheme DHroot_mut := Induction for DHroot Sort Type
with DHexp_mut := Induction for DHexp Sort Type
with DHtriv_mut := Induction for DHtriv Sort Type.

Coercion DHroot_exp : DHexp >-> DHroot.
Coercion DHexp_triv : DHtriv >-> DHexp.
Coercion DHtriv_var : var >-> DHtriv.

Hint Constructors DHroot DHexp DHtriv.

Fixpoint cps_htransform (r:DHroot) : Croot :=
match r with
| DHroot_exp e => cps_exp_htransform e (fun t => Cexp_cont t)
end
with cps_exp_htransform (e:DHexp) (k:Ctriv -> Cexp) : Cexp :=
match e with
| DHexp_app e0 e1 => cps_exp_htransform e0 (fun t0 =>
                     cps_exp_htransform e1 (fun t1 =>
                         Cexp_app t0 t1 0 (k (Ctriv_vvar 0))))
| DHexp_triv t    => k (cps_triv_htransform t)
end
with cps_triv_htransform (t:DHtriv) : Ctriv :=
match t with
| DHtriv_var x   => x
| DHtriv_vvar x  => Ctriv_vvar x
| DHtriv_lam x r => Ctriv_lam x (cps_htransform r)
end.

Fixpoint hole_triv_number (t:DHtriv) : nat :=
match t with
| DHtriv_var _   => 0
| DHtriv_lam _ _ => 0
| DHtriv_vvar _  => 1
end.

Fixpoint hole_exp_number (e:DHexp) : nat :=
match e with
| DHexp_triv t    => hole_triv_number t
| DHexp_app e0 e1 => hole_exp_number e0 + hole_exp_number e1
end.

Fixpoint hole_number (r:DHroot) : nat :=
match r with
| DHroot_exp e => hole_exp_number e
end.

Lemma hole_exp_valid :
  forall e:DHexp, hole_exp_number e = 0 ->
                  exists e':Dexp, forall k:Ctriv -> Cexp,
                                    cps_exp_htransform e k = cps_exp_transform e' k.
Proof.
induction e; intros; eauto; intuition.
inversion H; subst.
inversion H1; subst.
assert (hole_exp_number e1 = 0 /\ hole_exp_number e2 = 0).
apply plus_is_O; trivial.
destruct H0.
simpl.

specialize (IHe1 H0).
specialize (IHe2 H3).
destruct IHe1.
destruct IHe2.
exists (Dexp_app x x0).
intros.
simpl.
assert ((fun t0 : Ctriv =>
      cps_exp_htransform e2
        (fun t1 : Ctriv => Cexp_app t0 t1 0 (k (Ctriv_vvar 0)))) = (fun t0 : Ctriv =>
      cps_exp_transform x0
        (fun t1 : Ctriv => Cexp_app t0 t1 0 (k (Ctriv_vvar 0))))).
apply functional_extensionality.
intros.
rewrite H5.
trivial.
rewrite H6.
rewrite H4.
trivial.

inversion H; subst.
case_eq d; intros; subst; intuition.
exists (Dexp_triv (Dtriv_var v)); auto.
admit.
inversion H1.
Qed.

Fixpoint nonhole_trivial (e:DHexp) : bool :=
match e with
| DHexp_app _ _ => false
| DHexp_triv t  => match t with
                   | DHtriv_var _   => true
                   | DHtriv_lam _ _ => true
                   | DHtriv_vvar _  => false
                   end
end.

Fixpoint plug_triv (t:DHtriv) (e:DHexp) : DHexp :=
match t with
| DHtriv_var v   => DHtriv_var v
| DHtriv_lam x r => DHtriv_lam x r
| DHtriv_vvar _  => e
end.

Fixpoint plug_exp (e:DHexp) (e':DHexp) : DHexp :=
match e with
| DHexp_triv t    => plug_triv t e
| DHexp_app e0 e1 => if nonhole_trivial e0
                       then DHexp_app e0 (plug_exp e1 e')
                       else DHexp_app (plug_exp e0 e') e1
end.

Fixpoint plug (r:DHroot) (e:DHexp) : DHroot :=
match r with
| DHroot_exp e' => plug_exp e' e
end.

Lemma cps_plugging :
  forall (e:DHexp) (t0 t1:DHtriv) (v:var),
    not (hole_exp_number e = 0) ->
                  cps_exp_htransform (plug_exp e (DHexp_app t0 t1)) (fun t => Cexp_cont t) =
                  Cexp_app (cps_triv_htransform t0) (cps_triv_htransform t1) v
                           (cps_exp_htransform (plug_exp e (DHtriv_vvar v)) (fun t => Cexp_cont t)).
Proof.
induction e; eauto; simpl; intuition.
Admitted.

Lemma exp_v_plugging :
  forall (e:Cexp) (de:DHexp) (v:var) (vs:list var),
    CexpValid e (v::vs) -> cps_exp_htransform de (fun t => Cexp_cont t) = e ->
    plug_exp de (DHtriv_vvar v) = de.
Admitted.

Lemma holy_exp :
  forall (e:Cexp) (de:DHexp) (l:list var),
    CexpValid e l -> cps_exp_htransform de (fun t => Cexp_cont t) = e -> hole_exp_number de = length l.
Admitted.

Theorem super_theorem : forall r:Croot, CrootValid r -> exists dr:DHroot, cps_htransform dr = r.
Proof.
apply (CrootValid_mut (fun r rv => exists dr:DHroot, cps_htransform dr = r)
                      (fun t l0 l1 tv => exists dt:DHtriv, cps_triv_htransform dt = t)
                      (fun e l ev => exists de:DHexp, cps_exp_htransform de (fun t => Cexp_cont t) = e))
; eauto; intuition.
destruct H.
exists (DHroot_exp x).
simpl.
admit.

exists (DHtriv_vvar v).
simpl; trivial.

exists (DHtriv_var x).
simpl; trivial.

destruct H.
exists (DHtriv_lam x x0).
simpl.
rewrite H; trivial.

destruct H.
exists (x).
simpl.
rewrite H; trivial.

destruct H, H0, H1.
exists (plug_exp x1 (DHexp_app x0 x)).
rewrite cps_plugging with (v := v).
rewrite H.
rewrite H0.
rewrite -> exp_v_plugging with (e := e) (vs := ksi2).
rewrite H1.
trivial.
exact c1.
exact H1.

unfold not.
intros.
assert (hole_exp_number x1 = length (v::ksi2)).
apply holy_exp with (e := e); auto.
rewrite H2 in H3.
simpl in H3.
inversion H3.
Qed.
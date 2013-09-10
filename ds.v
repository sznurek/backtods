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
| Ctriv_vvar : Ctriv
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
| CtrivValid_vvar : forall (ksi:list var) (v:var), CtrivValid Ctriv_vvar (v::ksi) ksi
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

Definition Cont := Ctriv -> Cexp.

Fixpoint cps_transform (r:Droot) : Croot :=
match r with
| Droot_exp e => cps_exp_transform e (fun t => Cexp_cont t)
end
with cps_exp_transform (e:Dexp) (k:Cont) : Cexp :=
match e with
| Dexp_app e0 e1 => cps_exp_transform e0 (fun t0 =>
                    cps_exp_transform e1 (fun t1 =>
                        Cexp_app t0 t1 0 (k Ctriv_vvar)))
| Dexp_triv t    => k (cps_triv_transform t)
end
with cps_triv_transform (t:Dtriv) : Ctriv :=
match t with
| Dtriv_var x   => x
| Dtriv_lam x r => Ctriv_lam x (cps_transform r)
end.

Definition good_continuation (k:Cont) (s:list var) :=
  forall (t:Ctriv) (s':list var),
    CtrivValid t s' s -> CexpValid (k t) s'.

Hint Unfold good_continuation.

Theorem cps_transform_valid :
  forall r:Droot, CrootValid (cps_transform r).
Proof.
apply (Droot_mut (fun r => CrootValid (cps_transform r))
                 (fun e => forall (k:Cont) (s:list var),
                             good_continuation k s ->
                             CexpValid (cps_exp_transform e k) s)
                 (fun t => forall (s:list var), CtrivValid (cps_triv_transform t) s s));
intros; unfold good_continuation in *; eauto; simpl; intuition; eauto.
Qed.

Definition mold (e:Dexp) (rest:Cexp) : Cexp :=
  cps_exp_transform e (fun t => rest).

Lemma length_zero_is_nil :
  forall {A:Type} (es:list A), length es = 0 -> es = nil.
Proof.
intros.
destruct es.
trivial.
simpl in H.
inversion H.
Qed.

Definition is_app (e:Dexp) : Prop :=
match e with
| Dexp_app _ _ => True
| Dexp_triv _  => False
end.

Definition is_app_list (es:list Dexp) : Prop :=
  Forall is_app es.

Lemma app_produces_vvar :
  forall (e:Dexp), is_app e -> cps_exp_transform e (fun t => Cexp_cont t) =
                               cps_exp_transform e (fun _ => Cexp_cont Ctriv_vvar).
Proof.
induction e; intros; simpl in *; eauto.
inversion H.
Qed.

Theorem cps_inverse_exists :
  forall r:Croot, CrootValid r -> exists r':Droot, cps_transform r' = r.
Proof.
apply (CrootValid_mut
         (fun r rv => exists r':Droot, cps_transform r' = r)
         (fun t l0 l1 tv => (exists e, l0 = e::l1) \/
                            (exists e, cps_triv_transform e = t /\ l0 = l1))
         (fun e l ev => forall (es:list Dexp),
           length l = length es -> is_app_list es ->
           exists e':Dexp,
             cps_exp_transform e' (fun t => Cexp_cont t) =
             fold_right mold e es))
;intros; eauto; simpl in *; intuition.

specialize (H nil).
simpl in H.
specialize (H eq_refl (Forall_nil is_app)).
destruct H.
exists (Droot_exp x).
simpl.
admit. (*exact H.*)

right.
exists x.
simpl; auto.

right.
destruct H.
exists (Dtriv_lam x x0).
simpl; rewrite H; auto.

destruct H2; subst.
destruct es.
simpl in H0; inversion H0.
simpl in H0.
assert (es = nil).
apply length_zero_is_nil.
replace (length es) with (pred (S (length es))).
replace 0 with (pred (S 0)).
rewrite H0; simpl; trivial.
simpl; trivial.
simpl; trivial.
subst.
exists d.
unfold mold; simpl.
admit. (* mold is broken :( *)

admit. (* Just like up, mold is broken, but case is trivial. *)

destruct H4; destruct H; subst.
simpl in *.
specialize (H1 (Dexp_app x x0::es)).
simpl in H1.

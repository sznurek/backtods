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
| CexpValid_app  : forall (ksi0 ksi1 ksi2:list var) (t0 t1:Ctriv) (e:Cexp),
                     CtrivValid t1 ksi0 ksi1 -> CtrivValid t0 ksi1 ksi2 ->
                     CexpValid e (0::ksi2) ->
                     CexpValid (Cexp_app t0 t1 0 e) ksi0
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
intros; unfold good_continuation in *; simpl; eauto.
Qed.

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
  forall (e:Dexp) (k:Cont),
    is_app e -> cps_exp_transform e k =
                cps_exp_transform e (fun _ => k Ctriv_vvar).
Proof.
induction e; intros; simpl in *; eauto.
inversion H.
Qed.

Lemma has_exactly_one_element :
  forall {A:Type} (es:list A), length es = 1 -> exists a:A, es = a :: nil.
Proof.
intros; destruct es; auto.
inversion H.
exists a.
simpl in H.
assert (length es = 0).
replace (length es) with (pred (S (length es))).
replace 0 with (pred (S 0)).
rewrite H.
trivial.
trivial.
trivial.
destruct es; auto.
inversion H0.
Qed.

Lemma has_two_elements :
  forall {A:Type} (es:list A) (n:nat), length es = S (S n) ->
         exists (a b:A), exists es':list A, es = a::b::es'.
Proof.
intros.
destruct es; simpl in *; eauto.
inversion H.
destruct es.
simpl in H; inversion H.
destruct es.
exists a.
exists a0.
exists nil.
trivial.
exists a; exists a0; exists (a1::es); trivial.
Qed.

Lemma equal_arguments :
  forall {A B:Type} (f:A -> B) (x y:A), x = y -> f x = f y.
Proof.
intros; eauto.
rewrite H; auto.
Qed.

Definition mold (rest:Cexp) (e:Dexp) : Cexp :=
  cps_exp_transform e (fun t => rest).

Theorem cps_inverse_exists :
  forall r:Croot, CrootValid r -> exists r':Droot, cps_transform r' = r.
Proof.
apply (CrootValid_mut
         (fun r rv => exists r':Droot, cps_transform r' = r)
         (fun t l0 l1 tv => ((exists e, l0 = e::l1) /\ t = Ctriv_vvar) \/
                            (exists e, cps_triv_transform e = t /\ l0 = l1))
         (fun e l ev => forall (es:list Dexp),
           length l = length es -> is_app_list es ->
           exists e':Dexp,
             cps_exp_transform e' (fun t => Cexp_cont t) =
             fold_left mold es e))
;intros; eauto; simpl in *.

specialize (H nil).
simpl in H.
specialize (H eq_refl (Forall_nil is_app)).
destruct H.
exists (Droot_exp x).
simpl.
rewrite H.
trivial.

right.
exists x.
simpl; auto.

right.
destruct H.
exists (Dtriv_lam x x0).
simpl; rewrite H; auto.

destruct H.
destruct H.
destruct H.
subst.
simpl in H0.
symmetry in H0.
destruct es.
inversion H0.

assert (es = nil).
apply length_zero_is_nil.
replace (length es) with (pred (S (length es))).
replace 0 with (pred (S 0)).
simpl in H0; rewrite H0; simpl; trivial.
simpl; trivial.
simpl; trivial.
subst.
exists d.
unfold mold; simpl.
inversion c; subst.
apply app_produces_vvar.
unfold is_app_list in H1.
inversion H1; subst; auto.

destruct H; destruct H; subst.
exists x.
unfold mold; simpl.
symmetry in H0.
specialize (length_zero_is_nil es H0); intros; subst; simpl; auto.

intuition.
destruct H; destruct H0; subst; simpl in *.
symmetry in H2.
specialize (has_two_elements es (length ksi2) H2); intros.
destruct H.
destruct H.
destruct H.
subst.
specialize (H1 (Dexp_app x2 x1::x3)).
simpl in H1.
simpl in H2.
inversion H2.
rewrite H0 in H1.
specialize (H1 eq_refl).

assert (is_app_list (Dexp_app x2 x1 :: x3)).
constructor.
unfold is_app; simpl; auto.
inversion H3; subst.
inversion H6; subst.
trivial.

specialize (H1 H).
destruct H1.
exists x4.
simpl.
rewrite H1.
unfold mold.
simpl.

rewrite app_produces_vvar.
apply equal_arguments.
apply equal_arguments.

apply functional_extensionality; intros.
rewrite app_produces_vvar.
apply equal_arguments.
apply functional_extensionality; intros.
trivial.


inversion H3; trivial.
inversion H3; subst.
inversion H7; auto.

destruct H4.
destruct H0.
destruct H.
subst.

simpl in H2.
destruct es.
inversion H2.
simpl in H2.
specialize (H1 (Dexp_app x d::es)).
simpl in H1.
rewrite H2 in H1.
specialize (H1 eq_refl).

assert (is_app_list (Dexp_app x d :: es)).
constructor; simpl; auto.
inversion H3; subst; auto.
specialize (H1 H).
destruct H1.
exists x1.
simpl.
rewrite H0.
apply equal_arguments.
unfold mold; simpl.
apply app_produces_vvar.
inversion H3; trivial.




destruct H4.
destruct H0.
destruct H.
subst.

simpl in H2.
destruct es.
inversion H2.
simpl in H2.
specialize (H1 (Dexp_app d x::es)).
simpl in H1.
rewrite H2 in H1.
specialize (H1 eq_refl).

assert (is_app_list (Dexp_app d x :: es)).
constructor; simpl; auto.
inversion H3; subst; auto.
specialize (H1 H).
destruct H1.
exists x1.
simpl.
rewrite H0.
apply equal_arguments.
unfold mold; simpl.
apply app_produces_vvar.
inversion H3; trivial.


destruct H4, H; destruct H0, H; subst.
specialize (H1 (Dexp_app x0 x::es)).
simpl in H1; rewrite H2 in H1; specialize (H1 eq_refl).

assert (is_app_list (Dexp_app x0 x :: es)).
constructor; simpl; auto.
inversion H3; subst; auto.
Qed.



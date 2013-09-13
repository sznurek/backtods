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
| CexpValid_app  : forall (ksi0 ksi1 ksi2:list var) (t0 t1:Ctriv) (v:var) (e:Cexp),
                     CtrivValid t1 ksi0 ksi1 -> CtrivValid t0 ksi1 ksi2 ->
                     CexpValid e (v::ksi2) ->
                     CexpValid (Cexp_app t0 t1 0 e) ksi0
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

Definition Cont := var -> Ctriv -> Cexp.

Fixpoint cps_transform (r:Droot) : Croot :=
match r with
| Droot_exp e => cps_exp_transform 0 e (fun _ t => Cexp_cont t)
end
with cps_exp_transform (f:var) (e:Dexp) (k:Cont) : Cexp :=
match e with
| Dexp_app e0 e1 => cps_exp_transform (S f) e0 (fun f0 t0 =>
                    cps_exp_transform f0 e1 (fun f1 t1 =>
                        Cexp_app t0 t1 0 (k (S f1) (Ctriv_vvar f1))))
| Dexp_triv t    => k f (cps_triv_transform t)
end
with cps_triv_transform (t:Dtriv) : Ctriv :=
match t with
| Dtriv_var x   => x
| Dtriv_lam x r => Ctriv_lam x (cps_transform r)
end.

Definition good_continuation (k:Cont) (s:list var) :=
  forall (f:var) (t:Ctriv) (s':list var),
    CtrivValid t s' s -> CexpValid (k f t) s'.

Hint Unfold good_continuation.

Theorem cps_transform_valid :
  forall r:Droot, CrootValid (cps_transform r).
Proof.
apply (Droot_mut (fun r => CrootValid (cps_transform r))
                 (fun e => forall (k:Cont) (f:var) (s:list var),
                             good_continuation k s ->
                             CexpValid (cps_exp_transform f e k) s)
                 (fun t => forall (s:list var), CtrivValid (cps_triv_transform t) s s));
intros; unfold good_continuation in *; simpl; eauto.
Qed.

Lemma equal_arguments :
  forall {A B:Type} (f:A -> B) (x y:A), x = y -> f x = f y.
Proof.
intros; eauto.
rewrite H; auto.
Qed.

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

Lemma length_zero_is_nil :
  forall {A:Type} (es:list A), length es = 0 -> es = nil.
Proof.
intros A es H.
destruct es as [| x xs].
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
  forall (e:Dexp) (k:Cont) (f:var),
    is_app e -> exists (v:var), cps_exp_transform f e k =
                cps_exp_transform f e (fun n _ => k n (Ctriv_vvar v)).
Proof.
induction e; intros; eauto.
specialize (IHe1 (fun n0 t0 => cps_exp_transform n0 e2 k) f).
inversion H.
Admitted.

Lemma has_exactly_one_element :
  forall {A:Type} (es:list A), length es = 1 -> exists a:A, es = a :: nil.
Proof.
intros A es H; destruct es as [|x xs]; auto.
inversion H.
exists x.
simpl in H.
assert (length xs = 0).
replace (length xs) with (pred (S (length xs))).
replace 0 with (pred (S 0)).
rewrite H.
trivial.
trivial.
trivial.
destruct xs; auto.
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

Definition mold (f:var) (rest:Cexp) (e:Dexp) : Cexp :=
  cps_exp_transform f e (fun _ t => rest).

Definition a_eq (r1:Croot) (r2:Croot) := rename_v 0 r1 = rename_v 0 r2.
Definition a_exp_eq (e1:Cexp) (e2:Cexp) := rename_exp_v 0 e1 = rename_exp_v 0 e2.
Definition a_triv_eq (t1:Ctriv) (t2:Ctriv) :=
  rename_triv_v 0 t1 = rename_triv_v 0 t2.

Theorem cps_inverse_exists :
  forall r:Croot, CrootValid r -> exists r':Droot, a_eq (cps_transform r') r.
Proof.
apply (CrootValid_mut
         (fun r rv => exists r':Droot, a_eq (cps_transform r') r)
         (fun t l0 l1 tv => ((exists e, l0 = e::l1) /\ (exists v, t = Ctriv_vvar v)) \/
                            (exists e, a_triv_eq (cps_triv_transform e) t /\ l0 = l1))
         (fun e l ev => forall (f:var) (es:list Dexp),
           length l = length es -> is_app_list es ->
           exists e':Dexp,
             a_exp_eq (cps_exp_transform f e' (fun _ t => Cexp_cont t))
             (fold_left (mold f) es e)))
;intros; eauto; simpl in *.

specialize (H 0 nil).
simpl in H.
specialize (H eq_refl (Forall_nil is_app)).
destruct H.
exists (Droot_exp x).
simpl.
unfold a_eq.
unfold a_exp_eq in H.
simpl.
rewrite H.
trivial.

right.
exists x.
simpl; split; unfold a_triv_eq; simpl; auto.

right.
destruct H as [r'].
exists (Dtriv_lam x r').
unfold a_eq in H; simpl in H.
unfold a_triv_eq; split; simpl; auto.
rewrite H; trivial.

destruct H.
destruct H.
destruct H.
destruct H2.
subst.
simpl in H0.
symmetry in H0.
specialize (has_exactly_one_element es H0); intros.
destruct H as [d]; subst.

exists d.
unfold mold; simpl.
inversion c; subst.
specialize (app_produces_vvar d (fun _ t => Cexp_cont t) f); intros.
unfold is_app_list in H1.
inversion H1; subst.
specialize (H H4).
destruct H.
rewrite H.
unfold a_exp_eq; simpl.
admit. (* continuation v variable is whatever under the a_exp_eq *)


destruct H; destruct H; subst.
exists x.
unfold mold; simpl.
symmetry in H0.
specialize (length_zero_is_nil es H0); intros; subst; simpl; auto.
unfold a_exp_eq; simpl.
unfold a_triv_eq in H.
rewrite H; auto.

intuition.
destruct H, H0, H5, H6; subst; simpl in *; subst.
symmetry in H2.
specialize (has_two_elements es (length ksi2) H2); intros.
destruct H.
destruct H.
destruct H.
subst.
specialize (H1 (S f) (Dexp_app x4 x3::x5)).
simpl in H1.
simpl in H2.
inversion H2.
rewrite H0 in H1.
specialize (H1 eq_refl).

assert (is_app_list (Dexp_app x4 x3 :: x5)).
constructor.
unfold is_app; simpl; auto.
inversion H3; subst.
inversion H6; subst.
trivial.

specialize (H1 H).
destruct H1.
exists x6.
simpl.
unfold a_exp_eq in H1.
unfold a_exp_eq.
rewrite H1.
unfold mold.
simpl.

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



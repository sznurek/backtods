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

Fixpoint hole_triv_deep_number (t:DHtriv) : nat :=
match t with
| DHtriv_var _   => 0
| DHtriv_lam _ r => hole_deep_number r
| DHtriv_vvar _  => 1
end with hole_exp_deep_number (e:DHexp) : nat :=
match e with
| DHexp_triv t    => hole_triv_deep_number t
| DHexp_app e0 e1 => hole_exp_deep_number e0 + hole_exp_deep_number e1
end with hole_deep_number (r:DHroot) : nat :=
match r with
| DHroot_exp e => hole_exp_deep_number e
end.

Lemma deep_number_is_stronger :
  forall e:DHexp, hole_exp_number e <= hole_exp_deep_number e.
Proof.
apply (DHexp_mut (fun r => hole_number r <= hole_deep_number r)
                 (fun e => hole_exp_number e <= hole_exp_deep_number e)
                 (fun t => hole_triv_number t <= hole_triv_deep_number t))
;intros;simpl in *; eauto; intuition.
Qed.

Lemma hole_exp_valid :
  forall e:DHexp, hole_exp_deep_number e = 0 ->
                  exists e':Dexp, forall k:Ctriv -> Cexp,
                                    cps_exp_htransform e k = cps_exp_transform e' k.
Proof.
apply (DHexp_mut (fun r => hole_deep_number r = 0 -> exists r':Droot, cps_htransform r = cps_transform r')
                 (fun e => hole_exp_deep_number e = 0 ->
                           exists e':Dexp, forall k:Ctriv -> Cexp,
                             cps_exp_htransform e k = cps_exp_transform e' k)
                 (fun t => hole_triv_deep_number t = 0 ->
                           exists t':Dtriv, cps_triv_htransform t = cps_triv_transform t'))
; intros; simpl in *; eauto; intuition.
destruct H1.
exists (Droot_exp x).
rewrite H; auto.

specialize (plus_is_O (hole_exp_deep_number d) (hole_exp_deep_number d0) H1); intros.
destruct H2.
specialize (H H2).
specialize (H0 H3).
destruct H, H0.
exists (Dexp_app x x0).
intros.
simpl.
rewrite H.
assert ((fun t0 : Ctriv =>
      cps_exp_htransform d0
        (fun t1 : Ctriv => Cexp_app t0 t1 0 (k (Ctriv_vvar 0)))) = (fun t0 : Ctriv =>
      cps_exp_transform x0
        (fun t1 : Ctriv => Cexp_app t0 t1 0 (k (Ctriv_vvar 0))))).
apply functional_extensionality.
intros.
rewrite H0; auto.
rewrite H4; auto.

destruct H1.
exists x.
intros.
rewrite H; auto.
exists v; simpl; auto.
destruct H1.
exists (Dtriv_lam v x).
rewrite H; auto.
inversion H.
Qed.

Fixpoint plug_triv_aux (t:DHtriv) (e:DHexp) : (DHexp * bool) :=
match t with
| DHtriv_var v   => (DHexp_triv (DHtriv_var v), false)
| DHtriv_lam x r => (DHexp_triv (DHtriv_lam x r), false)
| DHtriv_vvar _  => (e, true)
end.

Fixpoint plug_exp_aux (e:DHexp) (e':DHexp) : (DHexp * bool) :=
match e with
| DHexp_triv t    => plug_triv_aux t e'
| DHexp_app e0 e1 => let a0 := plug_exp_aux e0 e' in
                     let a1 := plug_exp_aux e1 e' in
                     if snd a0
                       then (DHexp_app (fst a0) e1, true)
                       else (DHexp_app e0 (fst a1), snd a1)
end.

Definition plug_exp (e:DHexp) (e':DHexp) : DHexp :=
  fst (plug_exp_aux e e').

Lemma plug_exp_indicator :
  forall (e e0 e1:DHexp), snd (plug_exp_aux e e0) = snd (plug_exp_aux e e1).
Proof.
induction e.
intros a0 a1.
simpl.
rewrite IHe1 with (e0 := a1) (e2 := a0).
case_eq (snd (plug_exp_aux e1 a0)); intros; subst; simpl; auto.
intros.
case_eq d; intros; subst; simpl; auto.
Qed.

Lemma non_null_sum :
  forall n m:nat, n <> 0 -> n + m <> 0.
Proof.
intros.
omega.
Qed.

Lemma equi_neg :
  forall (A B:Prop), (A <-> B) -> ((~A) <-> (~B)).
Proof.
intros; tauto.
Qed.

Lemma plug_exp_holes :
  forall (e e':DHexp), snd (plug_exp_aux e e') = true <-> hole_exp_number e <> 0.
induction e; eauto; simpl.
intros; case_eq (snd (plug_exp_aux e1 e')); intros; subst; simpl; eauto.
split.
intro.
specialize (IHe1 e').
destruct IHe1.
specialize (H1 H).
assert (hole_exp_number e1 + hole_exp_number e2 <> 0) by (apply non_null_sum; eauto).
specialize (H2 H1); trivial.
auto.

split.
intros.
specialize (IHe2 e').
destruct (IHe2).
specialize (H1 H0).
assert (hole_exp_number e1 + hole_exp_number e2 <> 0) by (rewrite plus_comm; apply non_null_sum; eauto).
trivial.

intros.
apply IHe2.
specialize (IHe1 e').
specialize (equi_neg (snd (plug_exp_aux e1 e') = true) (hole_exp_number e1 <> 0) IHe1); intros.
destruct H1.
intro.
admit. (* Some arithmetic mumbo-jumbo. *)

intros.
split.
intros.
case_eq d; intros; subst; simpl in *; eauto.
inversion H.
inversion H.

intros.
case_eq d; intros; subst; simpl in *; eauto.
Qed.

Lemma cps_plugging :
  forall (e:DHexp) (t0 t1:DHtriv) (v:var) (k:Ctriv -> Cexp),
    not (hole_exp_number e = 0) ->
                  cps_exp_htransform (plug_exp e (DHexp_app t0 t1)) k =
                  Cexp_app (cps_triv_htransform t0) (cps_triv_htransform t1) v
                           (cps_exp_htransform (plug_exp e (DHtriv_vvar v)) k).
Proof.
induction e.
intros.
unfold plug_exp in *; simpl in *.
assert (snd (plug_exp_aux e1 (DHexp_app t0 t1)) = snd (plug_exp_aux e1 (DHtriv_vvar v))) by
    (apply plug_exp_indicator).
rewrite H0.
case_eq (snd (plug_exp_aux e1 (DHtriv_vvar v))); intros; subst; simpl; auto.
rewrite IHe1 with (v := v); simpl.
trivial.
apply plug_exp_holes with (e' := DHtriv_vvar v); auto.
Admitted.

Lemma exp_v_plugging :
  forall (e:Cexp) (de:DHexp) (v:var) (vs:list var),
    CexpValid e (v::vs) -> cps_exp_htransform de (fun t => Cexp_cont t) = e ->
    plug_exp de (DHtriv_vvar v) = de.
Proof.
induction de; intros; eauto; intuition; simpl in *; eauto.
unfold plug_exp in *; simpl; eauto.
case_eq (snd (plug_exp_aux de1 (DHtriv_vvar v))); intros; simpl.
Admitted.

Lemma plug_holes :
  forall e e':DHexp, hole_exp_number (plug_exp e e') = pred (hole_exp_number e) + hole_exp_number e'.
Proof.
induction e; unfold plug_exp in *; intros; simpl in *; eauto; intuition.
case_eq (snd (plug_exp_aux e1 e')); intros; subst; simpl in *; eauto.
rewrite IHe1.
case_eq (hole_exp_number e1); intros; subst; simpl in *.
specialize ((proj1 (plug_exp_holes e1 e')) H); intros.
specialize (H1 H0).
inversion H1.
rewrite <- plus_assoc.
rewrite (plus_comm (hole_exp_number e') (hole_exp_number e2)).
rewrite plus_assoc.
trivial.

rewrite IHe2; simpl.
case_eq (hole_exp_number e1); intros; subst; simpl in *; eauto.
specialize (plug_exp_holes e1 e'); intros.
Admitted.

Lemma minus_lemma :
  forall (n m p:nat), m <= n -> n <= p -> (n - m) + (p - n) = p - m.
Proof.
induction n.

intros.
simpl.
inversion H.
trivial.

intros.
destruct m; destruct p; simpl in *; eauto.
inversion H0.
rewrite le_plus_minus_r; trivial.
apply le_S_n; trivial.
rewrite plus_comm; simpl; auto.
inversion H0.
specialize (le_S_n m n H).
specialize (le_S_n n p H0).
intros.
specialize (IHn m p H2 H1).
trivial.
Qed.

Lemma triv_valid_list_le :
  forall (t:Ctriv) (l0 l1:list var), CtrivValid t l0 l1 -> length l1 <= length l0.
Proof.
intros.
inversion H; subst; simpl in *; eauto.
Qed.

(* TODO: Use the hole_exp_valid to get main result. *)
Theorem super_theorem : forall r:Croot, CrootValid r -> exists dr:DHroot, cps_htransform dr = r.
Proof.
apply (CrootValid_mut (fun r rv => exists dr:DHroot, cps_htransform dr = r)
                      (fun t l0 l1 tv => exists dt:DHtriv, cps_triv_htransform dt = t /\
                                         hole_triv_number dt = length l0 - length l1)
                      (fun e l ev => exists de:DHexp, cps_exp_htransform de (fun t => Cexp_cont t) = e /\
                                     hole_exp_number de = length l))
; eauto; intuition.
destruct H.
exists (DHroot_exp x).
simpl.
admit. (* Strange Coq behavior - I have goal in premises, but exact fails. *)

exists (DHtriv_vvar v).
split.
simpl; trivial.
simpl (length (v :: ksi)).
rewrite <- minus_Sn_m.
rewrite minus_diag.
simpl.
trivial.
auto.


exists (DHtriv_var x).
split.
simpl; trivial.
rewrite minus_diag; eauto.

destruct H.
exists (DHtriv_lam x x0).
split.
simpl.
rewrite H; trivial.
rewrite minus_diag; simpl; eauto.


destruct H.
destruct H.
exists (x).
split.
simpl.
rewrite H; trivial.
case_eq x; intros; subst; simpl; eauto; inversion c; subst; simpl; eauto.

destruct H, H0, H1.
destruct H, H0.
destruct H1.
exists (plug_exp x1 (DHexp_app x0 x)).
split.
rewrite cps_plugging with (v := v).
rewrite H.
rewrite H0.
rewrite -> exp_v_plugging with (e := e) (vs := ksi2).
rewrite H1.
trivial.
exact c1.
exact H1.
simpl in H4.
intro.
rewrite H5 in H4.
inversion H4.

rewrite plug_holes.
rewrite H4.
simpl.
rewrite H3.
rewrite H2.
rewrite minus_lemma.
rewrite le_plus_minus_r.
trivial.

apply le_trans with (m := length ksi1).
apply (triv_valid_list_le t0 ksi1 ksi2 c0).
apply (triv_valid_list_le t1 ksi0 ksi1 c).
apply (triv_valid_list_le t0 ksi1 ksi2 c0).
apply (triv_valid_list_le t1 ksi0 ksi1 c).
Qed.
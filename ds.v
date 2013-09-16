Require Import List.
Require Import Arith.Plus.
Require Import ZArith.
Require Import FunctionalExtensionality.
Require Import Setoid.

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

Definition Cont := var -> Ctriv -> Cexp.

Fixpoint cps_transform (r:Droot) : Croot :=
match r with
| Droot_exp e => cps_exp_transform 0 e (fun _ t => Cexp_cont t)
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

(* Main development below *)

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

Definition a_eq (r1:Croot) (r2:Croot) := rename_v 0 r1 = rename_v 0 r2.
Definition a_exp_eq (e1:Cexp) (e2:Cexp) := rename_exp_v 0 e1 = rename_exp_v 0 e2.
Definition a_triv_eq (t1:Ctriv) (t2:Ctriv) :=
  rename_triv_v 0 t1 = rename_triv_v 0 t2.

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

Definition nice_continuation (k:Cont) :=
  (forall (v n n' v0 v1:var), rename_exp_v v (k n (Ctriv_vvar v0)) = rename_exp_v v (k n' (Ctriv_vvar v1))) /\
  (forall (v n n':var) (t:Ctriv), rename_exp_v v (k n t) = rename_exp_v v (k n' t)).

Ltac destruct_exists :=
repeat match goal with
| [ H : exists _, _ |- _ ] => destruct H
end.

Ltac nice_cont := unfold nice_continuation; split; intros; simpl; eauto.

Ltac level_down :=
  apply equal_arguments; try (apply equal_arguments);
   try (apply functional_extensionality; intros); try (apply functional_extensionality; intros).

Lemma continuation_rename :
  forall (e:Dexp) (k:Cont) (v n f f':var), nice_continuation k ->
    rename_exp_v v (cps_exp_transform f e k) =
    rename_exp_v v (cps_exp_transform f' e (fun _ t => rename_exp_v v (k n t))).
Proof.
Hint Rewrite rename_exp_v_inv : rename.
induction e; intros; unfold nice_continuation in *; simpl; eauto; intuition; autorewrite with rename.
rewrite IHe1 with (n := 0) (f' := 0); autorewrite with rename.
symmetry.
rewrite IHe1 with (n := 0) (f' := 0); autorewrite with rename.
level_down.
rewrite IHe2 with (n := 0) (f' := 0); autorewrite with rename.
symmetry.
rewrite IHe2 with (n := 0) (f' := 0); autorewrite with rename.
simpl.
level_down.

autorewrite with rename.
rewrite H0 with (n' := n) (v1 := 0); auto.
split; intros; simpl.
rewrite H0 with (n' := S n') (v1 := n'); auto.
rewrite H0 with (n' := S n') (v1 := n'); auto.
split; intros; simpl.
rewrite rename_exp_v_inv.
rewrite rename_exp_v_inv.
rewrite H0 with (n' := n) (v1 := n'); auto.
rewrite rename_exp_v_inv.
rewrite rename_exp_v_inv.
rewrite H0 with (n' := n) (v1 := n'); auto.
split; intros; simpl.
rewrite IHe2 with (n := 0) (f' := 0).
symmetry.
rewrite IHe2 with (n := 0) (f' := 0).
simpl.
auto.
split; intros; simpl.
rewrite rename_exp_v_inv.
rewrite rename_exp_v_inv.
rewrite H0 with (n' := n) (v1 := n'0); auto.
rewrite rename_exp_v_inv.
rewrite rename_exp_v_inv.
rewrite H0 with (n' := n) (v1 := n'0); auto.
split; intros; simpl.
rewrite rename_exp_v_inv.
rewrite rename_exp_v_inv.
rewrite H0 with (n' := n) (v1 := n'0); auto.
rewrite rename_exp_v_inv.
rewrite rename_exp_v_inv.
rewrite H0 with (n' := n) (v1 := n'0); auto.
rewrite IHe2 with (n := 0) (f' := 0).
symmetry.
rewrite IHe2 with (n := 0) (f' := 0).
simpl; auto.
split; intros; simpl.
rewrite H0 with (n' := S n'0) (v1 := n'0); auto.
rewrite rename_exp_v_inv.
rewrite rename_exp_v_inv.
rewrite H0 with (n' := n) (v1 := n'0); auto.
rewrite rename_exp_v_inv.
rewrite rename_exp_v_inv.
rewrite H0 with (n' := n) (v1 := n'0); auto.
split; intros; simpl.
rewrite rename_exp_v_inv.
rewrite rename_exp_v_inv.
rewrite H0 with (n' := n) (v1 := n'0); auto.
rewrite rename_exp_v_inv.
rewrite rename_exp_v_inv.
rewrite H0 with (n' := n) (v1 := n'0); auto.
split; intros; simpl.
rewrite IHe2 with (n := 0) (f' := 0).
symmetry.
rewrite IHe2 with (n := 0) (f' := 0).
simpl; auto.
split; intros; simpl.
rewrite H0 with (n' := S n'0) (v1 := n'0); auto.
rewrite H0 with (n' := S n'0) (v1 := n'0); auto.
split; intros; simpl.
rewrite H0 with (n' := S n'0) (v1 := n'0); auto.
rewrite H0 with (n' := S n'0) (v1 := n'0); auto.
rewrite IHe2 with (n := 0) (f' := 0).
symmetry.
rewrite IHe2 with (n := 0) (f' := 0).
simpl; auto.
split; intros; simpl.
rewrite H0 with (n' := S n'0) (v1 := n'0); auto.
rewrite H0 with (n' := S n'0) (v1 := n'0); auto.
split; intros; simpl.
rewrite H0 with (n' := S n'0) (v1 := n'0); auto.
rewrite H0 with (n' := S n'0) (v1 := n'0); auto.

rewrite H1 with (n' := n); auto.
Qed.

Lemma continuation_rename_0 :
  forall (e:Dexp) (k:Cont) (v f:var), nice_continuation k ->
    rename_exp_v v (cps_exp_transform f e k) =
    rename_exp_v v (cps_exp_transform 0 e (fun _ t => rename_exp_v v (k 0 t))).
Proof.
intros; rewrite continuation_rename with (n := 0) (f' := 0); eauto.
Qed.

Lemma app_produces_vvar :
  forall (e:Dexp) (k:Cont) (v f f':var), is_app e -> nice_continuation k ->
    rename_exp_v v (cps_exp_transform f e k) =
    rename_exp_v v (cps_exp_transform f e (fun _ _ => k f' (Ctriv_vvar v))).
Proof.
destruct e; simpl in *; intros; eauto.
rewrite continuation_rename_0.
symmetry.
rewrite continuation_rename_0.
level_down.

rewrite continuation_rename_0.
symmetry.
rewrite continuation_rename_0.
level_down.

simpl.
unfold nice_continuation in H0; destruct H0.
rewrite H0 with (n' := f') (v1 := v); auto.

nice_cont.
unfold nice_continuation in H0; destruct H0.
rewrite H0 with (n' := (S n')) (v1 := n'); auto.

unfold nice_continuation in H0; destruct H0.
rewrite H0 with (n' := (S n')) (v1 := n'); auto.

nice_cont.
nice_cont.

rewrite continuation_rename_0.
symmetry.
rewrite continuation_rename_0.
level_down.
simpl.
auto.

nice_cont.
nice_cont.

rewrite continuation_rename_0.
symmetry.
rewrite continuation_rename_0.
level_down.
simpl.
auto.

nice_cont.
nice_cont.
nice_cont.

rewrite continuation_rename_0.
symmetry.
rewrite continuation_rename_0.
level_down.
simpl.
auto.

nice_cont.
unfold nice_continuation in H0; destruct H0.
rewrite H0 with (n' := (S n'0)) (v1 := n'0); auto.
unfold nice_continuation in H0; destruct H0.
rewrite H0 with (n' := (S n'0)) (v1 := n'0); auto.

nice_cont.
unfold nice_continuation in H0; destruct H0.
rewrite H0 with (n' := (S n'0)) (v1 := n'0); auto.
unfold nice_continuation in H0; destruct H0.
rewrite H0 with (n' := (S n'0)) (v1 := n'0); auto.

rewrite continuation_rename_0.
symmetry.
rewrite continuation_rename_0.
level_down.
simpl.
auto.

nice_cont.
unfold nice_continuation in H0; destruct H0.
rewrite H0 with (n' := (S n'0)) (v1 := n'0); auto.
unfold nice_continuation in H0; destruct H0.
rewrite H0 with (n' := (S n'0)) (v1 := n'0); auto.

nice_cont.
unfold nice_continuation in H0; destruct H0.
rewrite H0 with (n' := (S n'0)) (v1 := n'0); auto.
unfold nice_continuation in H0; destruct H0.
rewrite H0 with (n' := (S n'0)) (v1 := n'0); auto.
inversion H.
Qed.

Definition mold (rest:Cexp) (e:Dexp) : Cexp :=
  cps_exp_transform 0 e (fun _ t => rest).

Lemma fold_left_is_right :
  forall (ds:list Dexp) (c c':Cexp), a_exp_eq c c' -> a_exp_eq (fold_left mold ds c) (fold_left mold ds c').
Proof.
induction ds; intros; unfold a_exp_eq in *; simpl; eauto.
rewrite IHds with (c' := (mold c' a)); auto.
unfold mold; simpl.
rewrite continuation_rename_0.
symmetry.
rewrite continuation_rename_0.
rewrite H; auto.
unfold nice_continuation; split; intros; simpl; eauto.
unfold nice_continuation; split; intros; simpl; eauto.
Qed.

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

Lemma start_irrevelant :
  forall (e:Dexp) (k:Cont) (v f f':var), nice_continuation k ->
    rename_exp_v v (cps_exp_transform f e k) = rename_exp_v v (cps_exp_transform f' e k).
Proof.
intros.
rewrite continuation_rename_0.
symmetry.
rewrite continuation_rename_0.
auto.
auto.
auto.
Qed.

Ltac cont_rename := rewrite continuation_rename_0; [ idtac | nice_cont ].

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
             (fold_left mold es e)))
;intros; eauto; simpl in *.

(* Croot case *)
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

(* Ctriv_var case *)
right.
exists x.
simpl; split; unfold a_triv_eq; simpl; auto.

(* Ctriv_lam case *)
right.
destruct H as [r'].
exists (Dtriv_lam x r').
unfold a_eq in H; simpl in H.
unfold a_triv_eq; split; simpl; auto.
rewrite H; trivial.

(* Cexp_cont case *)
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
unfold a_exp_eq.
rewrite app_produces_vvar with (e := d) (v := 0) (f := f) (f' := 0).
rewrite continuation_rename with (v :=  0) (f := 0) (f' := f) (n := 0).
simpl; auto.
unfold nice_continuation; split; intros; simpl; eauto.

unfold is_app_list in H1.
inversion H1; subst.
assert (nice_continuation (fun (_:var) t => Cexp_cont t)).
unfold nice_continuation; split; intros; simpl; eauto.
auto.
unfold nice_continuation; split; intros; simpl; eauto.
destruct H.
exists x.
unfold a_exp_eq; simpl.
destruct H.
subst.
unfold a_triv_eq in H.
rewrite H.
symmetry in H0.
specialize (length_zero_is_nil es H0); intros; subst.
simpl; auto.

(* Cexp_app case *)
intuition; destruct_exists; subst; simpl in *; symmetry in H2.
(* v v case *)
specialize (has_two_elements es (length ksi2) H2); intros; destruct_exists; subst; simpl in *.
specialize (H1 f (Dexp_app x4 x3::x5)).
simpl in H1.
inversion H2.
rewrite H0 in H1.
specialize (H1 eq_refl).

assert (is_app_list (Dexp_app x4 x3 :: x5)).
constructor; simpl; eauto.
inversion H3; subst.
inversion H6; subst.
trivial.

specialize (H1 H).
destruct H1 as [e'].
exists e'.
unfold a_exp_eq in *.
rewrite H1.
apply fold_left_is_right.
unfold a_exp_eq; simpl.

unfold mold; simpl.
assert (forall t0:Ctriv, nice_continuation (fun f1 t1 => Cexp_app t0 t1 f1 e)) by nice_cont.
assert (nice_continuation (fun f0 t0 => cps_exp_transform f0 x3
                             (fun f1 t1 => Cexp_app t0 t1 f1 e))).
nice_cont.
cont_rename.
symmetry.
cont_rename.
level_down; simpl; auto.

rewrite start_irrevelant with (f' := n'); auto.
rewrite continuation_rename_0 with (e := x4) (f := 1); [ idtac | eauto; nice_cont ].
rewrite app_produces_vvar with (f' := 0).
rewrite app_produces_vvar with (f' := 0) (e := x3).
rewrite continuation_rename_0 with (e := x3); [ idtac | eauto; nice_cont ].
symmetry.
rewrite continuation_rename_0 with (e := x4); [ idtac | eauto; nice_cont ].
rewrite continuation_rename_0 with (e := x3); [ idtac | eauto; nice_cont ].
simpl.
auto.

unfold is_app_list in H3.
inversion H3.
auto.

nice_cont.

unfold is_app_list in H3.
inversion H3.
inversion H9; auto.

nice_cont.
rewrite rename_exp_v_inv.
rewrite rename_exp_v_inv.

rewrite continuation_rename_0.
symmetry.
rewrite continuation_rename_0.
simpl.
auto.

nice_cont.
nice_cont.

(* v t case *)
destruct H0; subst.
destruct es; [inversion H2 | idtac]; simpl in *.
specialize (H1 f (Dexp_app x d::es)).
inversion H2.
simpl in H1; rewrite H4 in H1.
specialize (H1 eq_refl).

inversion H3; subst.
assert (is_app_list (Dexp_app x d :: es)).
constructor; simpl; eauto.

specialize (H1 H0).
destruct H1 as [e'].
exists e'.
unfold a_exp_eq in *.
rewrite H1.
apply fold_left_is_right.
unfold mold.
unfold a_exp_eq.

assert (nice_continuation (fun _ _ => Cexp_app t0 (Ctriv_vvar x0) v e)) by nice_cont.

simpl.
cont_rename.
symmetry.
cont_rename.
simpl.
unfold a_triv_eq in H; rewrite H; auto.

symmetry.
rewrite app_produces_vvar with (f' := 0).
simpl; auto.
auto.
nice_cont.

(* t v case *)
destruct H4; subst.
destruct es; [inversion H2 | idtac]; simpl in *.
specialize (H1 f (Dexp_app d x1 ::es)).
inversion H2.
simpl in H1; rewrite H4 in H1.
specialize (H1 eq_refl).

inversion H3; subst.
assert (is_app_list (Dexp_app d x1 :: es)).
constructor; simpl; eauto.

specialize (H1 H0).
destruct H1 as [e'].
exists e'.
unfold a_exp_eq in *.
rewrite H1.
apply fold_left_is_right.
unfold mold.
unfold a_exp_eq.

assert (nice_continuation (fun _ _ => Cexp_app t1 (Ctriv_vvar x0) v e)) by nice_cont.

simpl.
cont_rename.
symmetry.
cont_rename.
simpl.

unfold a_triv_eq in H.
symmetry.
rewrite app_produces_vvar with (f' := 0).
simpl; auto.
rewrite <- H.
simpl; eauto.
auto.
nice_cont.

destruct H0; destruct H; subst.
rewrite <- H2 in H1.
specialize (H1 f (Dexp_app x x0 :: es) eq_refl).

assert (is_app_list (Dexp_app x x0 :: es)).
constructor; simpl; eauto.

specialize (H1 H4).
destruct H1 as [e'].
exists e'.
unfold a_exp_eq in *.
rewrite H1.
simpl.
unfold a_triv_eq in *.
apply fold_left_is_right.
unfold a_exp_eq; simpl.
rewrite H0.
rewrite H; auto.

Qed.

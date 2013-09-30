Require Import List.
Require Import Arith.Plus.
Require Import ZArith.
Require Import FunctionalExtensionality.
Require Import Setoid.

Require Import Terms.
Require Import Equivalence.
Require Import Transformations.

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

Lemma continuation_rename_0 :
  forall (e:Dexp) (k:Cont) (f v:var), nice_continuation k ->
    rename_exp_v v (cps_exp_transform f e k) =
    rename_exp_v v (cps_exp_transform 0 e (fun _ t => rename_exp_v v (k 0 t))).
Proof.
induction e; intros; unfold nice_continuation in H; simpl; intuition;
[rewrite IHe1; [symmetry; rewrite IHe1; [
      level_down
    | idtac]
  | idtac];

  repeat (simpl in *; match goal with
  | |- context[rename_exp_v _ (cps_exp_transform _ _ (fun f _ => Cexp_app _ _ f _)) =
               rename_exp_v _ (cps_exp_transform _ _ (fun g _ => Cexp_app _ _ g _))] =>
    (rewrite IHe2; [ symmetry; rewrite IHe2; [simpl; level_down | idtac] | idtac ])
  | |- context[rename_exp_v _ (rename_exp_v _ _)] => rewrite rename_exp_v_inv
  | |- nice_continuation _ => nice_cont
  | |- context [rename_exp_v _ (_ ?N (Ctriv_vvar ?V0))] => rewrite H0 with (n := N) (v0 := V0) (n' := 0) (v1 := 0)
  end; simpl in *; eauto)
| idtac ].

rewrite rename_exp_v_inv.
symmetry; rewrite H1 with (n' := f); auto.
Qed.

Ltac a_exp_eq_crusher :=
simpl; match goal with
| |- rename_exp_v _ (cps_exp_transform _ _ _) = rename_exp_v _ (cps_exp_transform _ _ _) =>
  rewrite continuation_rename_0; [ symmetry;
                                   rewrite continuation_rename_0;
                                   [level_down | idtac ] | idtac ]; idtac
| |- nice_continuation _ => nice_cont; idtac
end.

Lemma app_produces_vvar :
  forall (e:Dexp) (k:Cont) (v f f':var), is_app e -> nice_continuation k ->
    rename_exp_v v (cps_exp_transform f e k) =
    rename_exp_v v (cps_exp_transform f e (fun _ _ => k f' (Ctriv_vvar v))).
Proof.
destruct e; simpl in *; unfold nice_continuation; intros; eauto; intuition.
assert (forall v n v0:var, rename_exp_v v (k n (Ctriv_vvar v0)) =
                            rename_exp_v v (k 0 (Ctriv_vvar 0))) as R by eauto.

repeat (simpl in *; a_exp_eq_crusher); simpl; repeat (rewrite R; symmetry; eauto).
Qed.

Definition mold (rest:Cexp) (e:Dexp) : Cexp :=
  cps_exp_transform 0 e (fun _ t => rest).

Lemma fold_left_is_right :
  forall (ds:list Dexp) (c c':Cexp), a_exp_eq c c' -> a_exp_eq (fold_left mold ds c) (fold_left mold ds c').
Proof.
induction ds; intros; unfold a_exp_eq in *; simpl; eauto.
rewrite IHds with (c' := (mold c' a)); auto.
unfold mold; simpl.
rewrite continuation_rename_0; [ symmetry; rewrite continuation_rename_0; [ rewrite H; auto | nice_cont] | nice_cont ].
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
rewrite continuation_rename_0 with (f := f); auto.
rewrite continuation_rename_0 with (f := f'); auto.
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
exists (Dtriv_var x).
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
rewrite continuation_rename_0 with (v := 0) (f := 0).
rewrite continuation_rename_0 with (v := 0) (f := f).
simpl; auto.
nice_cont.
nice_cont.

unfold is_app_list in H1.
inversion H1; subst.
assert (nice_continuation (fun (_:var) t => Cexp_cont t)).
nice_cont.
auto.
nice_cont.
destruct H.
exists (Dexp_triv x).
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
specialize (H1 f (Dexp_app (Dexp_triv x) d::es)).
inversion H2.
simpl in H1; rewrite H4 in H1.
specialize (H1 eq_refl).

inversion H3; subst.
assert (is_app_list (Dexp_app (Dexp_triv x) d :: es)).
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
specialize (H1 f (Dexp_app d (Dexp_triv x1) ::es)).
inversion H2.
simpl in H1; rewrite H4 in H1.
specialize (H1 eq_refl).

inversion H3; subst.
assert (is_app_list (Dexp_app d (Dexp_triv x1) :: es)).
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
specialize (H1 f (Dexp_app (Dexp_triv x) (Dexp_triv x0) :: es) eq_refl).

assert (is_app_list (Dexp_app (Dexp_triv x) (Dexp_triv x0) :: es)).
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

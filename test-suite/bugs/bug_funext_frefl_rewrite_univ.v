(* Minimized from hierarchy-builder examples/cat/cat.v. *)
From Corelib Require Import ssreflect ssrfun.

Axiom funext : forall {A B} {f g : A -> B}, f =1 g -> f = g.
Axiom funext_frefl : forall {A B} (f : A -> B), funext (frefl f) = erefl.

Axiom P : forall B (F G : unit -> B) (eqFG : F =1 G),
  eq_rect _ (fun F0 => F0 tt = F0 tt) erefl _ (funext eqFG) = erefl -> F = G.

Goal forall B (F : unit -> B), (fun x => F x) = F.
Proof.
  move=> B F.
  apply/P; rewrite funext_frefl.
  reflexivity.
Qed.

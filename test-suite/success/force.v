(* To run: [dune build theories/Force && dune exec -- dev/shim/coqc test.v] *)

Require Import Force.Force.

(**** UNIVERSES ****)

Definition check_run@{u1 u2} : forall (T : Type@{u1}) (K : Type@{u2}), Blocked T -> (T -> K) -> K := @run.
Definition check_Blocked@{u} : Type@{u} -> Type@{u} := Blocked.
Definition check_block@{u} : forall (T : Type@{u}), T -> Blocked@{u} T := @block.
Definition check_unblock@{u} : forall (T : Type@{u}), Blocked@{u} T -> T := @unblock.

(**** EVALUATION ****)

Ltac syn_refl := lazymatch goal with |- ?t = ?t => exact eq_refl end.
Notation LAZY t := (ltac:(let x := eval lazy in t in exact x)) (only parsing).
Notation WHNF t := (ltac:(let x := eval lazywhnf  in t in exact x)) (only parsing).

Goal LAZY ((fun f => f (1 + 1)) block) = block (1 + 1).
Proof. syn_refl. Qed.

Goal LAZY ((fun f => f (1 + 1)) (fun x => block x)) = block (1 + 1).
Proof. syn_refl. Qed.

Goal WHNF ((fun f => f (1 + 1)) block) = block (1 + 1).
Proof. syn_refl. Qed.

Goal WHNF ((fun f => f (1 + 1)) (fun x => block x)) = block (1 + 1).
Proof. syn_refl. Qed.

Eval lazywhnf in run (block 0) (fun x => x).
Eval lazywhnf in run (block (1+1)) (fun x => x).

Eval lazywhnf in block (run (let n := 1 in block n) (fun x : nat => x)).

Eval lazywhnf in block (run (let x := (fun x => x) tt in block x) (fun x => x)).

Eval lazywhnf in block (unblock (let x := (fun x => x) tt in block x)).
(*
block (unblock (let x := (fun x => x) tt in block x)) @ ε | ∅ --{whnf}-->
block @ (unblock (let x := (fun x => x) tt in block x)) . ε | ∅ --{whnf}-->

  unblock (let x := (fun x => x) tt in block x) @ ε | ∅ --{id}-->
  unblock @ (let x := (fun x => x) tt in block x) . ε | ∅ --{id}-->

    let x := (fun x => x) tt in block x @ ε | ∅ --{full}-->
    block x @ ε | ∅[x{full} := <(fun x => x) tt, ∅>] --{full}-->

      x @ ε | ∅[x{full} := <(fun x => x) tt, ∅>] --{id}-->

        (λ x => x) tt @ ε | ∅ --{full}-->
        λ x => x @ tt . ε | ∅ --{full}-->
        x @ ε | ∅[x{full} := <tt, ∅>] --{full}-->

          tt @ ε | ∅ --{full}--> (value)

        tt @ ε | ∅[x{full} := <tt, ∅>] --{full}--> (value)

      tt @ ε | ∅[x{full} := <tt, ∅>] --{id}--> (value, updated closure)

    block tt @ ε | ∅[x{full} := <tt, ∅>] --{full}-->

  unblock @ block tt . ε | ∅ --{id}-->
  tt @ ε | ∅ --{id}-->

block @ tt . ε | ∅ --{whnf}--> (done)
*)

Goal WHNF (block (run (let n := 2 + 2 in block n) (fun x : nat => 2 * 1)))
        = (block ((fun _ : nat => 2 * 1) 4)).
Proof. syn_refl. Qed.

Goal WHNF (block (run ((fun n => block n) (2 + 2)) (fun x : nat => 2 * 1)))
        = (block ((fun _ : nat => 2 * 1) 4)).
Proof. syn_refl. Qed.

Goal WHNF (block (run ((fun n => block (n + 1)) (2 + 2)) (fun x : nat => 2 * 1)))
        = (block ((fun _ : nat => 2 * 1) (4 + 1))).
Proof. syn_refl. Qed.

Goal WHNF (block (run (let n := 2 + 2 in block (n + 1)) (fun x : nat => 2 * 1)))
        = (block ((fun _ : nat => 2 * 1) (4 + 1))).
Proof. syn_refl. Qed.

Goal WHNF (block (run ((fun n => block (n + 1)) 2) (fun x : nat => 2 * 1)))
        = (block ((fun _ : nat => 2 * 1) (2 + 1))).
Proof. syn_refl. Qed.

Goal WHNF (block (unblock (let n := 0 + 0 in block (n + n))))
        = block (0 + 0).
Proof. syn_refl. Qed.

Goal LAZY (run (block (1 + 1)) (fun x => x + x)) = 4.
Proof. syn_refl. Qed.

Goal LAZY (run (block (1 + 1)) (fun x => x + x)) = 4.
Proof. syn_refl. Qed.

Goal LAZY (run (block (1 + 1)) (fun x => x + x)) = 4.
Proof. syn_refl. Qed.

Goal LAZY (block (2 + 2)) = block (2 + 2).
Proof. syn_refl. Qed.

Goal LAZY (unblock (block 42)) = 42.
Proof. syn_refl. Qed.

Goal LAZY (unblock (block (2 + 2))) = 4.
Proof. syn_refl. Qed.

Goal LAZY (unblock ((fun _ => block (2 + 2)) tt)) = 4.
Proof. syn_refl. Qed.

Goal LAZY (block (fun x => (2 + 2) + x)) = block (fun x => (2 + 2) + x).
Proof. syn_refl. Qed.

Goal LAZY (unblock (block (fun x => (2 + 2) + x))) = fun x => S (S (S (S x))).
Proof. syn_refl. Qed.

Goal WHNF (run (let x := 1 + 1 in block (x + 1)) (fun x => forall y, y = x))
        = forall y, y = 2 + 1.
Proof. syn_refl. Qed.

Set Printing Width 1000.
Section AllArgs.
  Context (b : Blocked (nat -> nat)).
  Eval lazy in unblock b 0.

  Goal LAZY (unblock b 0) = unblock b 0.
  Proof. syn_refl. Qed.
End AllArgs.

(* Axiom F : run (let x := 1 + 1 in block (x + 1)) (fun x => forall y, y = x). *)
(* Goal True. let t := constr:(F 0) in let ty := type of t in idtac ty. Abort. *)

(* Axiom F : run (1 + 1) (fun x => forall y, y = x). *)
(* Goal True. let t := constr:(F 0) in match type of t with 0 = 2 => idtac end. Abort. *)

(* Axiom G : let x := 1 + 1 in forall y, y = x. *)
(* Goal True. let t := constr:(G 0) in match type of t with 0 = 1 + 1 => idtac end. Abort. *)

(* Axiom H : (fun x => forall y, y = x) (1 + 1). *)
(* Goal True. let t := constr:(H 0) in match type of t with 0 = 1 + 1 => idtac end. Abort. *)

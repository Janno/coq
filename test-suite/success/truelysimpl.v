Require Import Setoid.
Require Import Force.Force.
Require Import Ltac2.Ltac2.

Set Default Proof Mode "Classic".

Inductive prop :=
  | conj  : prop -> prop -> prop
  | true  : prop
  | false : prop
  | inj   : Blocked Prop -> prop.

Fixpoint reflect (p : prop) : Prop :=
  match p with
  | conj p1 p2 => reflect p1 /\ reflect p2
  | true       => True
  | false      => False
  | inj P      => unblock P
  end.

Fixpoint reflect2 (p : prop) : Blocked Prop :=
  match p with
  | conj p1 p2 => block ((unblock (reflect2 p1)) /\ (unblock (reflect2 p2)))
  | true       => block True
  | false      => block False
  | inj P      => P
  end.

Ltac2 rec reify (p : constr) : constr :=
  lazy_match! p with
  | ?p1 /\ ?p2 => let p1 := reify p1 in let p2 := reify p2 in '(conj $p1 $p2)
  | True       => '(true)
  | False      => '(false)
  | ?p         => '(inj (block $p))
  end.

Fixpoint simplify (p : prop) : prop :=
  match p with
  | conj p1 p2 =>
      match simplify p1 with
      | true  => simplify p2
      | false => false
      | p1    =>
          match simplify p2 with
          | true  => p1
          | false => false
          | p2    => conj p1 p2
          end
      end
  | _ => p
  end.

Lemma iff_trivial (P : Prop) : P <-> P.
Proof. split; intros H; exact H. Qed.

Lemma and_comm (P1 P2 : Prop) : P1 /\ P2 <-> P2 /\ P1.
Proof.
  split.
  - intros [H1 H2]; split; [exact H2 | exact H1].
  - intros [H2 H1]; split; [exact H1 | exact H2].
Qed.

Lemma and_true (P : Prop) : P /\ True <-> P.
Proof.
  split.
  - intros [HP _]. exact HP.
  - intros HP. split; [exact HP| exact I].
Qed.

Lemma true_and (P : Prop) : True /\ P <-> P.
Proof. rewrite and_comm. rewrite and_true. apply iff_trivial. Qed.

Lemma and_false (P : Prop) : P /\ False <-> False.
Proof.
  split.
  - intros [_ HF]. exact HF.
  - intros HF. exfalso. exact HF.
Qed.

Lemma false_and (P : Prop) : False /\ P <-> False.
Proof. rewrite and_comm. rewrite and_false. apply iff_trivial. Qed.

Lemma simplify_ok (p : prop) : reflect (simplify p) <-> reflect p.
Proof.
  induction p; simpl.
  - rewrite <-IHp1; clear IHp1.
    rewrite <-IHp2; clear IHp2.
    destruct (simplify p1).
    + destruct (simplify p2); simpl.
      * apply iff_trivial.
      * rewrite and_true. apply iff_trivial.
      * rewrite and_false. apply iff_trivial.
      * apply iff_trivial.
    + simpl. rewrite true_and. apply iff_trivial.
    + simpl. rewrite false_and. apply iff_trivial.
    + destruct (simplify p2); simpl.
      * apply iff_trivial.
      * rewrite and_true. apply iff_trivial.
      * rewrite and_false. apply iff_trivial.
      * apply iff_trivial.
  - apply iff_trivial.
  - apply iff_trivial.
  - apply iff_trivial.
Qed.

Eval simpl in reflect2 (conj true (inj (block (1 + 1 = 2)))).

(*

run {T} : Blocked T -> (T -> K) -> K

The new idea is to reduce [run t f] as follows:
- evaluate [t] to a normal form [block u],
- evaluate all "unblocked" subterms inside [u] recursively
  (without touching the intermediate parts of the term)
  to get to a term [v],
- continue with [f v].

*)

Lemma simplify_ok_run (p : prop) :
  run (reflect (simplify p) -> reflect p) (fun x => x).
Proof. simpl. apply simplify_ok. Qed.

Lemma simplify_ok_run2 (p : prop) :
  run (unblock (reflect2 (simplify p)) -> unblock (reflect2 p)) (fun x => x).
Proof. Admitted.

Ltac2 redflags_all := {
  Std.rBeta  := true;
  Std.rDelta := true;
  Std.rMatch := true;
  Std.rFix   := true;
  Std.rCofix := true;
  Std.rZeta  := true;
  Std.rConst := []
}.

Ltac2 redflags_none := {
  Std.rBeta  := false;
  Std.rDelta := false;
  Std.rMatch := false;
  Std.rFix   := false;
  Std.rCofix := false;
  Std.rZeta  := false;
  Std.rConst := []
}.

Ltac2 truely_simplify (p : constr) : unit :=
  let reified := reify p in
  let simplified := '(reflect (simplify $reified)) in
  let simplified :=
    let bl := [reference:(unblock)] in
    let flags := {redflags_all with Std.rConst := bl} in
    Std.eval_lazy flags simplified
  in
  let simplified :=
    let wl := [reference:(unblock); reference:(block)] in
    let flags := {redflags_none with Std.rConst := wl} in
    Std.eval_lazy flags simplified
  in
  let subgoal := Std.eval_hnf (open_constr:(_ : $simplified)) in
  let x := '(simplify_ok_run $reified) in
  apply (($x : $simplified -> $p) $subgoal).

Ltac truely_simplify :=
  let truely_simplify :=
    ltac2:(p |- truely_simplify (Option.get (Ltac1.to_constr p)))
  in
  lazymatch goal with |- ?p => unshelve truely_simplify p end.

Ltac2 truely_simplify2 (p : constr) : unit :=
  let reified := reify p in
  let x := '(simplify_ok_run $reified) in
  refine x.

Ltac truely_simplify2 :=
  let truely_simplify :=
    ltac2:(p |- truely_simplify2 (Option.get (Ltac1.to_constr p)))
  in
  lazymatch goal with |- ?p => unshelve truely_simplify p end.

Goal True /\ (True /\ 1 + 1 = 2) /\ (True /\ True /\ 2 + 1 = 3).
Proof.
  truely_simplify2.
  split; reflexivity.
  Show Proof.
Qed.

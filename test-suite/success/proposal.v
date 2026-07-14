Require Import Corelib.Force.

Inductive prop :=
  | conj  : prop -> prop -> prop
  | true  : prop
  | false : prop
  | inj   : Blocked Prop -> prop.

Fixpoint reflect (p : prop) : Blocked Prop :=
  match p with
  | conj p1 p2 =>
      __block Prop (
          (__unblock Prop (reflect p1))
       /\ (__unblock Prop (reflect p2))
      )
  | true       => __block Prop True
  | false      => __block Prop False
  | inj P      => P
  end.

Require Import Ltac2.Ltac2.
Set Default Proof Mode "Classic".

Ltac2 rec reify (p : constr) : constr :=
  lazy_match! p with
  | ?p1 /\ ?p2 => let p1 := reify p1 in let p2 := reify p2 in '(conj $p1 $p2)
  | True       => '(true)
  | False      => '(false)
  | ?p         => '(inj (__block Prop $p))
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

Lemma simplify_ok_run (p : prop) :
  __run Prop Prop (
      __block Prop (
          __unblock Prop (reflect (simplify p)) ->
          __unblock Prop (reflect p)))
    (fun x => x).
Admitted.

Ltac2 simplify (p : constr) : unit :=
  let reified := reify p in
  let p := '(simplify_ok_run $reified _) in
  refine p.

Ltac simplify :=
  let simplify2 :=
    ltac2:(p |- simplify (Option.get (Ltac1.to_constr p)))
  in
  lazymatch goal with |- ?p => unshelve simplify2 p end.

Goal True /\ (True /\ True) /\ (1 = 1 /\ True /\ True).
Proof.
  simplify.
  reflexivity.
Qed.

Fixpoint ack (n m : nat) : nat :=
  match n with
  | O => S m
  | S p => let fix ackn (m : nat) :=
               match m with
               | O => ack p 1
               | S q => ack p (ackn q)
               end
           in ackn m
  end.

Goal True /\ ack 4 3 = 0.
Proof.
  simplify.
Abort.

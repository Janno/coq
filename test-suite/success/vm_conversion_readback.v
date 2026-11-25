Definition hidden_nat (b : bool) := if b then nat else bool.

(* The ordinary VM cast is still available with the option off. *)
Definition direct : nat := (O <: hidden_nat true).

Set VM Conversion Readback.

Definition readback : nat := (O <: hidden_nat true).
Fail Definition bad_readback : bool := (O <: hidden_nat false).

(* A neutral scrutinee leaves a suspended switch for readback. *)
Definition neutral (b : bool) (x : hidden_nat b) : hidden_nat b :=
  (x <: match b with true => nat | false => bool end).

(* Force universe inference during elaboration of a cast between types. *)
Set Universe Polymorphism.
Definition identity_type@{u} (A : Type@{u}) := A.
Definition polymorphic@{u} (A : Type@{u}) (a : A) :=
  (a <: identity_type A).

(* Exercise the kernel directly, bypassing cast checking in elaboration. *)
Goal hidden_nat true.
Proof.
  vm_cast_no_check O.
Qed.

Goal hidden_nat false.
Proof.
  vm_cast_no_check O.
Fail Qed.
Abort.

Unset VM Conversion Readback.
Definition direct_again : nat := (O <: hidden_nat true).

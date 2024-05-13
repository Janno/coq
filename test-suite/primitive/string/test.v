Require Import Uint63 PrimString.

Open Scope uint63_scope.
Open Scope pstring_scope.

Check (eq_refl : length (make 0              "a") = 0         ).
Check (eq_refl : length (make 42             "a") = 42        ).
Check (eq_refl : length (make max_length     "a") = max_length).
Check (eq_refl : length (make (max_length+1) "a") = max_length).

Check (eq_refl : make 0 "a" = "").
Check (eq_refl : make 5 "a" = "aaaaa").

Check (eq_refl : get "abcdefg" 0 = "a"%char63).
Check (eq_refl : get "abcdefg" 5 = "f"%char63).
Check (eq_refl : get "abcdefg" 6 = "g"%char63).

(* Invalid index. *)
Check (eq_refl : get "abcdefg" 7 = "000"%char63).

Check (eq_refl : sub "abcdefg" 0 0 = "").
Check (eq_refl : sub "abcdefg" 0 7 = "abcdefg").
Check (eq_refl : sub "abcdefg" 0 6 = "abcdef").
Check (eq_refl : sub "abcdefg" 1 6 = "bcdefg").
Check (eq_refl : sub "abcdefg" 6 1 = "g").
Check (eq_refl : sub "abcdefg" 6 0 = "").
Check (eq_refl : sub "abcdefg" 7 0 = "").

(* Invalid ranges. *)
Check (eq_refl : sub "abcdefg" 7 2 = "").
Check (eq_refl : sub "abcdefg" 73 42 = "").

Check (eq_refl : cat ""   ""   = ""  ).
Check (eq_refl : cat "a"  "b"  = "ab").
Check (eq_refl : cat "aa" ""   = "aa").
Check (eq_refl : cat ""   "bb" = "bb").

Check (eq_refl : compare ""   ""   = Eq).
Check (eq_refl : compare "a"  ""   = Gt).
Check (eq_refl : compare ""   "a"  = Lt).
Check (eq_refl : compare "a"  "b"  = Lt).
Check (eq_refl : compare "b"  "a"  = Gt).
Check (eq_refl : compare "a"  "ab" = Lt).
Check (eq_refl : compare "ab" "a"  = Gt).

Ltac syntactic_refl :=
  lazymatch goal with
  | |- ?x = ?x => apply (@eq_refl _ x)
  end.

Goal make 5 "a" = cat (make 2 "a") (make 3 "a").
Proof. lazy. syntactic_refl. Qed.

Goal make 5 "a" = cat (make 2 "a") (make 3 "a").
Proof. cbn. syntactic_refl. Qed.

Goal make 5 "a" = cat (make 2 "a") (make 3 "a").
Proof. cbv. syntactic_refl. Qed.

(* [vm_compute] *)

Goal make 5 "a" = cat (make 2 "a") (make 3 "a").
Proof. vm_compute. syntactic_refl. Qed.

Goal get "aaa" 0 = "a"%char63.
Proof. vm_compute. syntactic_refl. Qed.

Goal sub "abcd" 2 1 = "c".
Proof. vm_compute. syntactic_refl. Qed.

Goal cat "ab" "ba" = "abba".
Proof. vm_compute. syntactic_refl. Qed.

Goal compare "ab" "ab" = Eq.
Proof. vm_compute. syntactic_refl. Qed.

Goal compare "ab" "a" = Gt.
Proof. vm_compute. syntactic_refl. Qed.

Goal compare "a" "ab" = Lt.
Proof. vm_compute. syntactic_refl. Qed.

(* [native_compute] *)

Goal make 5 "a" = cat (make 2 "a") (make 3 "a").
Proof. native_compute. syntactic_refl. Qed.

Goal get "aaa" 0 = "a"%char63.
Proof. native_compute. syntactic_refl. Qed.

Goal sub "abcd" 2 1 = "c".
Proof. native_compute. syntactic_refl. Qed.

Goal cat "ab" "ba" = "abba".
Proof. native_compute. syntactic_refl. Qed.

Goal compare "ab" "ab" = Eq.
Proof. native_compute. syntactic_refl. Qed.

Goal compare "ab" "a" = Gt.
Proof. native_compute. syntactic_refl. Qed.

Goal compare "a" "ab" = Lt.
Proof. native_compute. syntactic_refl. Qed.

Require Import Uint63.
Require Import PrimString.

(** * Properties of string length *)

Axiom valid_length :
  forall s, length_valid (length s).

Axiom make_length_spec :
  forall i c,
    length_valid i ->
    length (make i c) = i.

Axiom sub_length_spec :
  forall s off len,
    range_valid s off len ->
    length (sub s off len) = len.

Axiom cat_length_spec :
  forall s1 s2,
    length_valid (length s1 + length s2)%uint63 ->
    (length (cat s1 s2) = length s1 + length s2)%uint63.

(** * Properties of string get *)

Axiom get_valid :
  forall s i,
    (i <? length s = true)%uint63 ->
    char63_valid (get s i).

Axiom make_get_spec :
  forall i j c,
    length_valid i ->
    (j <? i = true)%uint63 ->
    get (make i c) j = (c land 255)%uint63.

Axiom sub_get_spec :
  forall s off len i,
    range_valid s off len ->
    (i <? len = true)%uint63 ->
    get (sub s off len) i = get s (off + i).

Axiom cat_get_spec_l :
  forall s1 s2 i,
    length_valid (length s1 + length s2)%uint63 ->
    (i <? length s1 = true)%uint63 ->
    get (cat s1 s2) i = get s1 i.

Axiom cat_get_spec_r :
  forall s1 s2 i,
    length_valid (length s1 + length s2)%uint63 ->
    (i <? length s1 = false)%uint63 ->
    (i <? length s1 + length s2 = true)%uint63 ->
    get (cat s1 s2) i = get s2 (i - length s1).

(** * Properties of string comparison *)

Axiom compare_spec :
  forall s1 s2 c,
    compare s1 s2 = c <->
    exists i,
      (i <=? length s1 = true)%uint63 /\
      (i <=? length s2 = true)%uint63 /\
      (forall j, (j <? i = true)%uint63 -> get s1 j = get s2 j) /\
      match (i =? length s1, i =? length s2)%uint63 with
      | (true , true ) => c = Eq
      | (true , false) => c = Lt
      | (false, true ) => c = Gt
      | (false, false) =>
          match Uint63.compare (get s1 i) (get s2 i) with
          | Eq => False
          | ci => c = ci
          end
      end.

Axiom string_eq_correct :
  forall s1 s2 : string, string_eq s1 s2 -> s1 = s2.

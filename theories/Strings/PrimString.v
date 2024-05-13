Require Import Uint63.

Definition char63 := int.

Definition char63_valid (c : char63) :=
  (c land 255 = c)%uint63.

Module Export Char63Notations.
  Declare Scope char63_scope.
  Delimit Scope char63_scope with char63.
  String Notation int id_int id_int : char63_scope.
End Char63Notations.

Primitive string := #string_type.

Module Export PStringNotations.
  Record string_wrapper := wrap_string {string_wrap : string}.
  Definition id_string (s : string) : string := s.
  Register string as strings.pstring.type.
  Register string_wrapper as strings.pstring.string_wrapper.
  Register wrap_string as strings.pstring.wrap_string.

  Declare Scope pstring_scope.
  Delimit Scope pstring_scope with pstring.
  String Notation string id_string id_string : pstring_scope.
End PStringNotations.

Primitive max_length : int := #string_max_length.

Primitive make : int -> char63 -> string := #string_make.
Arguments make _%_uint63 _%_char63.

Primitive length : string -> int := #string_length.
Arguments length _%_pstring.

Primitive get : string -> int -> char63 := #string_get.
Arguments get _%_pstring _%_uint63.

Primitive sub : string -> int -> int -> string := #string_sub.
Arguments sub _%_pstring _%_uint63 _%_uint63.

Primitive cat : string -> string -> string := #string_cat.
Arguments sub _%_pstring _%_pstring.

Primitive compare : string -> string -> comparison := #string_compare.
Arguments compare _%_pstring _%_pstring.

Definition string_eq (s1 s2 : string) : Prop := compare s1 s2 = Eq.
Definition string_lt (s1 s2 : string) : Prop := compare s1 s2 = Lt.
Definition string_gt (s1 s2 : string) : Prop := compare s1 s2 = Gt.
Definition string_ne (s1 s2 : string) : Prop := not (string_eq s1 s2).
Definition string_le (s1 s2 : string) : Prop := not (string_gt s1 s2).
Definition string_ge (s1 s2 : string) : Prop := not (string_lt s1 s2).

Definition empty : string := ""%pstring.

Definition length_valid (i : int) : Prop :=
  (i <=? max_length = true)%uint63.

Definition range_valid (s : string) (off len : int) : Prop :=
  (off <=? length s = true /\ len <=? length s - off = true)%uint63.

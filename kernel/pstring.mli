(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Primitive [string] type. *)

type t = string

type char63 = Uint63.t

val max_length_int : int
val max_length : Uint63.t

(** [make i c] returns a string of size [min i max_length] containing only the
    character with code [c l_and 255]. *)
val make : Uint63.t -> char63 -> string

(** [length s] gives the length of string [s]. *)
val length : string -> Uint63.t

(** [get s i] gives the code of the character stored at index [i] in [s]. When
    index [i] is invalid, the function returns zero. *)
val get : string -> Uint63.t -> char63

(** [sub s off len] returns the substring of [s] starting at offset [off], and
    of length [len]. If [off] and [len] do not identify a valid substring then
    [""] is returned. In particular, [sub s (length s) 0] yields [""]. *)
val sub : string -> Uint63.t -> Uint63.t -> string

(** [cat s1 s2] returns the concatenation of strings [s1] and [s2]. If the
    combined length of these two strings is larger than [max_length], an empty
    string [""] is returned. *)
val cat : string -> string -> string

(** [compare s1 s2] returns [0] if [s1] and [s2] are equal, a number less than
    [0] if [s1] is smaller than [s2], and a number greater than [0] if [s1] is
    greater than [s2]. *)
val compare : string -> string -> int

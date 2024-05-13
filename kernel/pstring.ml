(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t = string

type char63 = Uint63.t

(* Maximum length on a 32-bits system. *)
let max_length_int : int = 16777211

let max_length : Uint63.t = Uint63.of_int max_length_int

(* Return a string of size [max_length] if the parameter is too large.
   Use [c land 255] if [c] is not a valid character. *)
let make : Uint63.t -> char63 -> string = fun i c ->
  let i = Uint63.to_int_min i max_length_int in
  let c = Uint63.l_and c (Uint63.of_int 255) in
  let c = Char.chr (Uint63.to_int_min c 255) in
  String.make i c

let length : string -> Uint63.t = fun s ->
  Uint63.of_int (String.length s)

(* Out of bound access gives '\x00'. *)
let get : string -> Uint63.t -> char63 = fun s i ->
  let i = Uint63.to_int_min i max_length_int in
  if i < String.length s then
    Uint63.of_int (Char.code (String.get s i))
  else
    Uint63.zero

(* Invalid offset/length yields an empty string. *)
let sub : string -> Uint63.t -> Uint63.t -> string = fun s off len ->
  let off = Uint63.to_int_min off max_int in
  let len = Uint63.to_int_min len max_int in
  try String.sub s off len with Invalid_argument _ -> ""

(* Gives an empty string if the combined length of the parameters would
   overflow the maximum string size. *)
let cat : string -> string -> string = fun s1 s2 ->
  let len1 = String.length s1 in
  let len2 = String.length s2 in
  if len1 + len2 <= max_length_int then s1 ^ s2 else ""

let compare : string -> string -> int =
  String.compare

(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let res_pf ?with_evars ?with_classes ?flags clenv =
  Feedback.msg_notice Pp.(str "will be applied using evarconv in the future");
  Clenv.res_pf ?with_evars ?with_classes ?flags clenv

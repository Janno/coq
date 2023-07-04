(* Contents copied and adapted from
   https://github.com/coq-community/metaprogramming-rosetta-stone/blob/48e92067d6c8170a996c42ed88b221bd7ab4ebbd/real_simplifier/ltac2_reflexive/theories/RealSimpl.v
*)



(** * Reflexive tactic to compute real expressions using Q arithmetic *)

(** This is similar to field_simplify, but
    - it handles min and max
    - it is easier to extend with additional functions which are computable in Q (like modulus)
    - it does not change the term structure except for computation (which can be an advantage or disadvantage)

    A few notes:
    - this is a reflexive tactic, which means the relevant context (a ℝ term) is converted to a gallina data structure and the
      majority of the work (the simplification and computation) is done by gallina functions
    - the advantage of reflexive tactics is that one can prove upfront that the transformations done by gallina functions are correct
    - in this case this means the equality of the original and simplified term is proven by application of a generic lemma
    - this is much faster than constructing and type checking equality lemmas for individual cases
    - reflexive tactics typically have these components:
      - a reification tactic which converts the relevant context to an AST in gallina
      - an interpretation tactic which converts the AST back to the original term (the inverse of reification)
      - some processing function on the AST (written in gallina)
      - a proof that the processing function has certain properties (in this case preserves equality in ℝ of the interpretation of the AST)
      - a wrapper tactic, which does the reification, posts the above proof, computes in the type of the proof and applies this in some form
    - this specific instance of a reflexive tactic takes a short cut:
      - terms which are not "understood" by the tactic, say variables or unknown functions are copied literally
      - not converting the handled terms fully to an AST type and relying on computation with explicit delta lists is "quick and dirty" but quite effective
      - the correctness proofs tend to be substantially more complicated if some form of context management is required
      - the down side of this method is that if the user supplied term or context does contain symbols of the domain the tactic computes in (ℚ, ℤ, pos in this case)
        the terms can blow up
      - to avoid this one option is to copy the Q, Z and Pos functions used and use these copies (assuming that these copies do not occur in the user supplied term)

    Caveats:
    - this tactic does ℚ, ℤ and Pos computation on parts of the supplied term
    - if the term includes computations with variables in these domains, the term might explode
*)

Require Import Reals.
Require Import ZArith.
Require Import QArith.
Require Import Lra.
Require Import Lia.
Require Import Ltac2.Ltac2.
Require Import Ltac2.Printf.
Require Import Ltac2.Bool.
Require Import Force.Force.

Notation delay x := (unblock (block x)).

(** ** Definition of the AST *)

Inductive Expr_UnaryOp :=
  | EU_Opp
  | EU_Inv
.

Inductive Expr_BinaryOp :=
  | EB_Add
  | EB_Sub
  | EB_Mul
  | EB_Div
  | EB_Max
  | EB_Min
.

(** For a nat value we need only two variants - something we can compute and something we can't (like a variable) *)

Inductive Expr_N : Set :=
  | EN_lit  : nat -> Expr_N (* This is used for everything we can evaluate *)
  | EN_gen  : Blocked nat -> Expr_N (* This is used for everything we cannot evaluate *)
.

Inductive Expr_R : Set :=
  | ER_Q      : Q -> Expr_R (* This is used for everything we can evaluate *)
  | ER_R      : Blocked R -> Expr_R (* This is used for everything we cannot evaluate *)
  | ER_Z      : Z -> Expr_R (* We could use Q for Z, but then interpretation would not be an inverse of reification *)
  | ER_Unary  : Expr_UnaryOp -> Expr_R -> Expr_R
  | ER_Binary : Expr_BinaryOp -> Expr_R -> Expr_R -> Expr_R
  | ER_Pow    : Expr_R -> Expr_N -> Expr_R
.

(** ** Interpretation and simplification functions for ℕ *)

(** For ℕ this is trivial, since it anyway computes *)

Definition interpret_N (e : Expr_N) : nat :=
  match e with
  | EN_lit n => delay n
  | EN_gen n => unblock n
  end.

(** ** Interpretation and simplification functions for ℝ *)

(** Return the ℝ function corresponding to an unary operator *)

Definition unary_fun_R (f : Expr_UnaryOp) : R->R :=
  match f with
  | EU_Opp => delay Ropp
  | EU_Inv => delay Rinv
  end.

(** Return the ℝ function corresponding to a binary operator *)

Definition binary_fun_R (f : Expr_BinaryOp) : R->R->R :=
  match f with
  | EB_Add => delay Rplus
  | EB_Sub => delay Rminus
  | EB_Mul => delay Rmult
  | EB_Div => delay Rdiv
  | EB_Max => delay Rmax
  | EB_Min => delay Rmin
  end.

(** Return the ℚ function corresponding to an unary operator *)

Definition unary_fun_Q (f : Expr_UnaryOp) : Q->Q :=
  match f with
  | EU_Opp => Qopp
  | EU_Inv => Qinv
  end.

(** Return the ℚ function corresponding to a binary operator *)

Definition binary_fun_Q (f : Expr_BinaryOp) : Q->Q->Q :=
  match f with
  | EB_Add => Qplus
  | EB_Sub => Qminus
  | EB_Mul => Qmult
  | EB_Div => Qdiv
  | EB_Max => Qminmax.Qmax
  | EB_Min => Qminmax.Qmin
  end.

(** Check if the argument of an unary operator is valid (that is not inversion of 0) *)

Definition unary_check_args_Q (f : Expr_UnaryOp) (a : Q) : bool :=
  match f with
  | EU_Inv => negb ((Qnum a) =? 0)%Z
  | _ => true
  end.

(** Check if the arguments of a binary operator are valid (that is not division by 0) *)

Definition binary_check_args_Q (f : Expr_BinaryOp) (a b : Q) : bool :=
  match f with
  | EB_Div => negb ((Qnum b) =? 0)%Z
  | _ => true
  end.

(** Interpret an AST, that is convert it back to a ℝ term - this function and the reification tactic must be inverse *)

Fixpoint interpret_R (e : Expr_R) : R :=
  match e with
  | ER_Q q => delay Q2R q
  | ER_R r => (unblock r)
  | ER_Z z => delay IZR z
  | ER_Unary f a => (unary_fun_R f) (interpret_R a)
  | ER_Binary f a b => (binary_fun_R f) (interpret_R a) (interpret_R b)
  | ER_Pow a b => delay pow (interpret_R a) (interpret_N b)
  end.

(** Simplify an AST by computation using ℚ arithmetic *)

Fixpoint simplify_R (e : Expr_R) : Expr_R :=
  match e with
  | ER_Q q => ER_Q q
  | ER_R r => ER_R r
  | ER_Z z => ER_Q (z#1)
  | ER_Unary f a =>
    let a':=simplify_R a in
    match a' with
    | ER_Q aq =>
      if unary_check_args_Q f aq
      then ER_Q ((unary_fun_Q f) aq)
      else ER_Unary f a'
    | _ => ER_Unary f a'
    end
  | ER_Binary f a b =>
    let a':=simplify_R a in
    let b':=simplify_R b in
    match a', b' with
    | ER_Q aq, ER_Q bq =>
      if binary_check_args_Q f aq bq
      then ER_Q ((binary_fun_Q f) aq bq)
      else ER_Binary f a' b'
    | _, _ => ER_Binary f a' b'
    end
  | ER_Pow a b =>
    let a':=simplify_R a in
    match a', b with
    | ER_Q aq, EN_lit bn => ER_Q (Qpower aq (Z.of_nat bn))
    | _, _ => ER_Pow a' b
    end
end.

(** Convert resulting "Q2R (n#d)" terms to quotients of integers in ℝ - or an integer if the denominator is 1 *)

(* ToDo: do reduction of Q as well *)

Fixpoint cleanup_R (e : Expr_R) : Expr_R :=
  match e with
  | ER_Q (z # 1) => ER_Z z
  | ER_Q (n # d) => ER_Binary EB_Div (ER_Z n) (ER_Z (Z.pos d))
  | ER_R r => e
  | ER_Z z => e
  | ER_Unary f a => ER_Unary f (cleanup_R a)
  | ER_Binary f a b => ER_Binary f (cleanup_R a) (cleanup_R b)
  | ER_Pow a b => ER_Pow (cleanup_R a) b
  end.

(** ** Proofs that the simplification and cleanup functions are correct *)

(** *** ℚ ℝ arithmetic equivalence lemmas missing in the standard library *)

Lemma Q2R_max: forall x y : Q,
  Q2R (Qminmax.Qmax x y) = Rmax (Q2R x) (Q2R y).
Proof.
  intros x y.
  destruct (Qlt_le_dec x y) as [Hlt|Hle].
  - rewrite Qminmax.Q.max_r, Rmax_right.
    + reflexivity.
    + apply Qreals.Qle_Rle, Qlt_le_weak, Hlt.
    + apply Qlt_le_weak, Hlt. (* Not sure why lra doesn't work here *)
  - rewrite Qminmax.Q.max_l, Rmax_left.
    + reflexivity.
    + apply Qreals.Qle_Rle, Hle.
    + apply Hle.
Qed.

Lemma Q2R_min: forall x y : Q,
  Q2R (Qminmax.Qmin x y) = Rmin (Q2R x) (Q2R y).
Proof.
  intros x y.
  destruct (Qlt_le_dec x y) as [Hlt|Hle].
  - rewrite Qminmax.Q.min_l, Rmin_left.
    + reflexivity.
    + apply Qreals.Qle_Rle, Qlt_le_weak, Hlt.
    + apply Qlt_le_weak, Hlt.
  - rewrite Qminmax.Q.min_r, Rmin_right.
    + reflexivity.
    + apply Qreals.Qle_Rle, Hle.
    + apply Hle.
Qed.

Lemma Qpower_nat_succ: forall (x : Q) (n : nat),
  Qpower x (Z.of_nat (S n)) = x * Qpower x (Z.of_nat n).
Proof.
  (* This is a bit tedious because most lemmas about Q use == instead of =, but we want = here *)
  intros x n.
  induction n.
  - cbn. unfold Qmult. cbn.
    rewrite Z.mul_1_r, Pos.mul_1_r.
    destruct x as [n d].
    reflexivity.
  - cbn.
    unfold Qpower_positive.
    rewrite pow_pos_succ.
    + reflexivity.
    + apply Eqsth.
    + unfold Proper, respectful; intros; subst; reflexivity.
    + intros a b c. unfold Qmult. destruct a, b, c. cbn.
      rewrite Z.mul_assoc.
      rewrite Pos.mul_assoc.
      reflexivity.
Qed.

Lemma Q2R_pow: forall (x : Q) (n : nat),
  (Q2R x ^ n)%R = Q2R (x ^ Z.of_nat n).
Proof.
  intros x n.
  induction n.
  - cbn. unfold Q2R. cbn. ltac1:(lra).
  - rewrite Qpower_nat_succ. cbn.
    rewrite Qreals.Q2R_mult.
    rewrite IHn.
    reflexivity.
Qed.

(** *** Correctness lemmas for ℝ*)

(** The interpretation of a term before and after cleanup_R is equal in ℝ *)

Lemma cleanup_R_correct: forall (e : Expr_R),
  interpret_R e = interpret_R (cleanup_R e).
Proof.
  intros e; induction e as [q|r|z|f a IHa|f a IHa b IHb|a IHa b].
  - (* Q *) cbn.
    destruct q as [n d]; destruct d; try (lazy; reflexivity).
    unfold Q2R; cbn; lazy; ltac1:(lra).
  - (* R *) reflexivity.
  - (* Z *) reflexivity.
  - (* unary *) cbn. rewrite IHa. reflexivity.
  - (* binary *) cbn; rewrite IHa, IHb; reflexivity.
  - (* pow *) cbn; rewrite IHa; reflexivity.
Qed.

(** The interpretation of a term before and after simplification is equal in ℝ *)

Lemma simplify_R_correct: forall (e : Expr_R),
  interpret_R e = interpret_R (simplify_R e).
Proof.
  intros e; induction e as [q|r|z|f a IHa|f a IHa b IHb|a IHa b].
  - (* Q *) reflexivity.
  - (* R *) reflexivity.
  - (* Z *) cbn; lazy [block unblock]; unfold Q2R; cbn; ltac1:(lra).
  - (* unary *) cbn.
    destruct (simplify_R a); rewrite IHa; try reflexivity.
    cbn.
    destruct f; cbn; lazy [block unblock].
    + rewrite Qreals.Q2R_opp; reflexivity.
    + destruct (Z.eqb_spec (Qnum q) 0) as [Heq|Hneq]; cbn; lazy [block unblock].
      * reflexivity.
      * rewrite Qreals.Q2R_inv.
        1: reflexivity.
        unfold Qeq; cbn.
        ltac1:(lia).
  - (* binary *) cbn.
    destruct (simplify_R a) as [qa| | | | |]; rewrite IHa;
    destruct (simplify_R b) as [qb| | | | |]; rewrite IHb; try reflexivity.
    cbn; lazy [block unblock].
    destruct f; cbn; lazy [block unblock].
    + rewrite Qreals.Q2R_plus; reflexivity.
    + rewrite Qreals.Q2R_minus; reflexivity.
    + rewrite Qreals.Q2R_mult; reflexivity.
    + destruct (Z.eqb_spec (Qnum qb) 0) as [Heq|Hneq]; cbn; lazy [block unblock].
      * reflexivity.
      * rewrite Qreals.Q2R_div.
        1: reflexivity.
        unfold Qeq; cbn; lazy [block unblock].
        ltac1:(lia).
    + rewrite Q2R_max; reflexivity.
    + rewrite Q2R_min; reflexivity.
  - (* Pow *) cbn; lazy [block unblock].
    destruct (simplify_R a); rewrite IHa; try reflexivity.
    destruct b; cbn; lazy [block unblock]; try reflexivity.
    apply Q2R_pow.
Qed.

(** The interpretation of a term before and after simplification and cleanup_R is equal in ℝ *)

Lemma cleanup_simplify_R_correct: forall (e : Expr_R),
  run (
      interpret_R e = interpret_R (cleanup_R (simplify_R e))
    ) (fun x => x).
Proof.
  intros e.
  rewrite <- cleanup_R_correct.
  hnf.
  apply simplify_R_correct.
Qed.

(** ** Reification and main tactic *)

(** *** Debugging *)

(** These notations are intended to wrap printf and can be defined to t() or () to enable / disable the prints.
    dbg1 is for low verbosity output, dbg2 for high verbosity output *)

Ltac2 Notation "dbg1" t(thunk(tactic(6))) := ().
Ltac2 Notation "dbg2" t(thunk(tactic(6))) := ().

(** *** Term classification *)

(** Check if "val" is a literal positive *)

Ltac2 rec is_literal_positive (val : constr) : bool :=
  lazy_match! val with
  | xI ?sub => is_literal_positive sub
  | xO ?sub => is_literal_positive sub
  | xH => true
  | _ => false
  end.

(** Check if "val" is a literal ℤ *)

Ltac2 is_literal_Z (val : constr) : bool :=
  lazy_match! val with
  | Z0 => true
  | Zpos ?pos => is_literal_positive pos
  | Zneg ?pos => is_literal_positive pos
  | _ => false
  end.

(** Check if "val" is a literal ℚ *)

Ltac2 is_literal_Q (val : constr) : bool :=
  lazy_match! val with
  | (?n # ?d)%Q => is_literal_Z n && is_literal_positive d
  | _ => false
  end.

(** Check if "val" is a computable nat *)

Ltac2 rec is_computable_nat (val : constr) : bool :=
  lazy_match! val with
  | (?a + ?b)%nat => is_computable_nat a && is_computable_nat b
  | (?a - ?b)%nat => is_computable_nat a && is_computable_nat b
  | (?a * ?b)%nat => is_computable_nat a && is_computable_nat b
  | S ?a => is_computable_nat a
  | O => true
  | _ => false
  end.

(** *** Reification *)

(** This converts a term in ℝ to a Expr_R AST structure - this tactic and "interpret_R" must be inverse to each other *)

(** Note: we can't prove that the tactic and "interpret_R" are inverses - if they are not the tactic will fail when trying to unify the term in the goal with the interpreted AST.
    Probably if the reification would be done in MetaCoq, one could prove this. *)

Ltac2 rec reify_Expr_N (e : constr) : constr :=
  (dbg2 printf "=> reify_Expr_N %t" e);
  let res := lazy_match! e with
  | Z.to_nat ?z => if is_literal_Z z then '(EN_lit $e) else '(EN_gen (block $e))
  | ?n          => if is_computable_nat n then '(EN_lit $n) else '(EN_gen (block $n))
  end in
  (dbg2 printf "<= reify_Expr_N %t" res);
  res.

Ltac2 rec reify_Expr_R (e : constr) : constr :=
  (dbg2 printf "=> reify_Expr_R %t" e);
  let res := lazy_match! e with
  | IZR ?z      => if is_literal_Z z then '(ER_Z $z) else '(ER_R $e)
  | Q2R ?q      => if is_literal_Q q then '(ER_Q $q) else '(ER_R $e)
  | (- ?a)%R    => let a':=reify_Expr_R a in '(ER_Unary EU_Opp $a')
  | (/ ?a)%R    => let a':=reify_Expr_R a in '(ER_Unary EU_Inv $a')
  | (?a + ?b)%R => let a':=reify_Expr_R a in let b':=reify_Expr_R b in '(ER_Binary EB_Add $a' $b')
  | (?a - ?b)%R => let a':=reify_Expr_R a in let b':=reify_Expr_R b in '(ER_Binary EB_Sub $a' $b')
  | (?a * ?b)%R => let a':=reify_Expr_R a in let b':=reify_Expr_R b in '(ER_Binary EB_Mul $a' $b')
  | (?a / ?b)%R => let a':=reify_Expr_R a in let b':=reify_Expr_R b in '(ER_Binary EB_Div $a' $b')
  | Rmax ?a ?b  => let a':=reify_Expr_R a in let b':=reify_Expr_R b in '(ER_Binary EB_Max $a' $b')
  | Rmin ?a ?b  => let a':=reify_Expr_R a in let b':=reify_Expr_R b in '(ER_Binary EB_Min $a' $b')
  | (?a ^ ?b)%R => let a':=reify_Expr_R a in let b':=reify_Expr_N b in '(ER_Pow $a' $b')
  | ?a          => '(ER_R (block $a))
  end in
  (dbg2 printf "<= reify_Expr_R %t" res);
  res.

(** *** Main tactic "real_simplify" *)


Ltac2 redflags_all_but_unblock () :=
  {
    (* beta: expand the application of an unfolded functions by substitution *)
    Std.rBeta := true;
    (* delta: true = expand all but rConst; false = expand only rConst *)
    Std.rDelta := true;
    (* Note: iota in tactics like cbv is a shorthand for match, fix and cofix *)
    (* iota-match: simplify_R matches by choosing a pattern *)
    Std.rMatch := true;
    (* iota-fix: simplify_R fixpoint expressions by expanding one level *)
    Std.rFix := true;
    (* iota-cofix: simplify_R cofixpoint expressions by expanding one level *)
    Std.rCofix := true;
    (* zeta: expand let expressions by substitution *)
    Std.rZeta := true;
    (* Symbols to expand *)
    Std.rConst := [reference:(unblock)]
  }.

Ltac2 redflags_only_unblock () :=
  {
    Std.rBeta := false;
    Std.rDelta := false;
    Std.rMatch := false;
    Std.rFix := false;
    Std.rCofix := false;
    Std.rZeta := false;
    (* Symbols to expand *)
    Std.rConst := [reference:(unblock); reference:(block)]
  }.

Ltac2 real_simplify (term : constr) (rhs : constr) : unit :=
  (dbg1 printf "real_simplify: term = %t" term);
  let ast := reify_Expr_R term in
  (dbg1 printf "real_simplify: AST = %t" ast);
  let subgoal := Std.eval_lazy (redflags_all_but_unblock ()) '(interpret_R (cleanup_R (simplify_R $ast))) in
  let subgoal := Std.eval_lazy (redflags_only_unblock ()) subgoal in
  let subgoal := open_constr:(_ : $subgoal = $rhs) in
  let subgoal := Std.eval_hnf subgoal in
  let eq := '(cleanup_simplify_R_correct $ast) in
  (* let eq_ty := Std.eval_lazy (redflags_all_but_unblock ()) (Constr.type eq) in *)
  (* let eq_ty := Std.eval_lazy (redflags_only_unblock ()) eq_ty in *)
  (* TODO: unification doesn't understand [run] *)
  let prf :=
    Constr.Unsafe.make (Constr.Unsafe.App '(eq_ind_r (x:=$rhs) (fun x => x = $rhs)) (Array.of_list [subgoal; term; eq]))
  in
  Std.exact_no_check prf.

(** An Ltac1 wrapper for the tactic *)

Ltac real_simplify := ltac2:(term |- real_simplify (Option.get (Ltac1.to_constr term))).

(** ** Tests *)

Section Test.
Variable x : R.
Open Scope R.

Goal (x+(Rmax ((3*4+5^2-6)/7) (1/2)) = x + 31/7).
  lazy_match! goal with [ |- (?a = ?b) ] => real_simplify a b end.
  Unshelve.
  reflexivity.
Qed.

End Test.

Eval rered head in 1 + 1.

Arguments Nat.add _ !_.

(* Set Debug "rered". *)
Eval rered head in 1 + (1 + 1).

Axiom x : nat.
Eval rered head in x + 1.
Eval rered head in 1 + x.
Eval rered head in 1 + (x + 1).

(* motivating example *)

Inductive type : Set :=
    Tptr : type -> type
  | Tref : type -> type
  | Trv_ref : type -> type
  | Tint : type -> type -> type
  | Tvoid : type
  | Tarray : type -> type -> type
  | Tnamed : type -> type
  | Tfunction : type -> type -> type -> type
  | Tbool : type
  | Tmember_pointer : type -> type -> type
  | Tfloat : type -> type
  | Tqualified : type -> type -> type
  | Tnullptr : type
  | Tnullptr1 : type
  | Tnullptr2 : type
  | Tnullptr3 : type
  | Tnullptr4 : type
  | Tnullptr5 : type
  | Tnullptr6 : type
  | Tnullptr7 : type
  | Tnullptr8 : type
  | Tnullptr9 : type
  | Tnullptr10 : type
  | Tnullptr11 : type
  | Tnullptr12 : type
  | Tnullptr13 : type
  | Tnullptr14 : type
  | Tnullptr15 : type
  | Tnullptr16 : type
  | Tnullptr17 : type
  | Tnullptr18 : type
  | Tnullptr19 : type
  | Tnullptr20 : type
  | Tnullptr21 : type
  | Tnullptr22 : type
  | Tnullptr23 : type
  | Tnullptr24 : type
  | Tnullptr25 : type
  | Tnullptr26 : type
  | Tnullptr27 : type
  | Tnullptr28 : type
  | Tnullptr29 : type
  | Tarch : type -> type -> type
  | Tbla : bla -> type
  | Tblu : blu -> type
with bla :=
| bla1 : type -> bla
| bla2 : type -> bla
| bla3 : type -> bla
| bla4 : type -> bla
with blu :=
| blu1 : type -> blu
| blu2 : type -> blu
| blu3 : type -> blu
| blu4 : type -> blu
.


  #[local] Notation EQ_DEC T := (forall x y : T, {x = y} + {~ x = y}) (only parsing).

  Lemma type_eq_dec' : EQ_DEC type
  with bla_eq_dec' : EQ_DEC bla
  with blu_eq_dec' : EQ_DEC blu.
  Proof.
    all: intros x y.
    all: pose (type_eq_dec' : EQ_DEC type).
    all: pose (bla_eq_dec' : EQ_DEC bla).
    all: pose (blu_eq_dec' : EQ_DEC blu).
    all: decide equality.
  Defined.

  Definition type_eq_dec := Eval lazy zeta delta [type_eq_dec'] in type_eq_dec'.
  Definition bla_eq_dec :=  Eval lazy zeta delta [bla_eq_dec']  in bla_eq_dec'.
  Definition blu_eq_dec :=  Eval lazy zeta delta [blu_eq_dec']  in blu_eq_dec'.

(* Definition type_eq_dec : forall (ty1 ty2 : type), { ty1 = ty2 } + { ty1 <> ty2 }. *)
(* Proof. *)
(*   fix IHty1 1.  decide equality. *)
(*   revert b. *)
(*   fix IHbla 1. decide equality. *)
(*   revert b. *)
(*   fix IHbla 1. decide equality. *)
(* Defined. *)

Definition Decision := fun P : Prop => {P} + {~ P}.
Definition RelDecision := fun {A B : Type} (R : A -> B -> Prop) => forall (x : A) (y : B), Decision (R x y).
Definition bool_decide {P:Prop} : {P} + {~P} -> bool :=
    fun x => match x with | left _ => true | right _ => false end.
Definition decide_rel {A B : Type} (R : A -> B -> Prop) (RelDecision : RelDecision R) : forall (x : A) (y : B), Decision (R x y) :=
  RelDecision.

Eval rered in bool_decide (decide_rel _ (fun x y => left eq_refl) 1 1).

(* Arguments bool_decide : simpl nomatch. *)
(* Arguments decide_rel. *)

(* Goal forall ty1 ty2 r, decide_rel _ type_eq_dec ty1 ty2 = r. *)
(* Proof. *)
(*   intros. *)
(*   (* Set Debug "RAKAM". *) *)
(*   (* Redirect "/tmp/rakam" *) *)
(*     cbn. *)

Goal (if if bool_decide (decide_rel _ type_eq_dec Tvoid Tvoid) then true else false then True else False).
  Succeed time "lazy " lazy.       (* Tactic call lazy  ran for 0. secs (0.u,0.s) (success) *)
  Succeed time "cbv  " cbv.        (* Tactic call cbv   ran for 0. secs (0.u,0.s) (success) *)
  Succeed time "vm   " vm_compute. (* Tactic call vm    ran for 0. secs (0.u,0.s) (success) *)
  Succeed time "simpl" simpl.      (* Tactic call simpl ran for 0.062 secs (0.061u,0.s) (su *)
  Succeed time "cbn  " cbn.        (* Tactic call cbn   ran for 0.707 secs (0.706u,0.s) (su *)
  Succeed time "rered" rered.      (* Tactic call rered ran for 0. secs (0.u,0.s) (success) *)
Abort.

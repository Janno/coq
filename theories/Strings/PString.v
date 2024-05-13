Require Import Uint63.
Require Export PrimString.
Require Export PrimStringAxioms.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.ZifyUint63.
Require Import Coq.micromega.Zify.
Require Import Coq.Numbers.Cyclic.Int63.Ring63.
Require Import ZArith.

Lemma length_ok (s : string) : (to_Z (length s) <= to_Z max_int)%Z.
Proof.
  pose proof (Uint63.to_Z_bounded (length s)) as [_ H]; revert H.
  unfold wB, size, max_int.
  assert (to_Z 9223372036854775807 = 9223372036854775807%Z) as -> by reflexivity.
  assert (2 ^ Z.of_nat 63 = 9223372036854775808)%Z as -> by reflexivity. lia.
Qed.

Lemma make_get_spec_valid (i j : int) (c : char63) :
  length_valid i ->
  char63_valid c ->
  (j <? i = true)%uint63 ->
  get (make i c) j = c.
Proof.
  intros. rewrite make_get_spec; assumption.
Qed.

#[local] Ltac case_if :=
  lazymatch goal with
  | |- context C [if ?b then _ else _] => destruct b eqn:?
  | H : context C [if ?b then _ else _] |- _ => destruct b eqn:?
  end.

Lemma string_eq_ext (s1 s2 : string) :
  string_eq s1 s2 <->
    (length s1 = length s2 /\
       forall i, (i <? length s1 = true)%uint63 -> get s1 i = get s2 i).
Proof.
  unfold string_eq. rewrite compare_spec. split.
  - intros [i (H1 & H2 & Hget & H)].
    rewrite !Uint63.compare_def_spec in H; unfold compare_def in H.
    repeat case_if; try inversion H; split.
    + apply Uint63.eqb_correct. lia.
    + intros. apply Hget. lia.
  - intros [-> H]. exists (length s2). rewrite eqb_refl.
    repeat split; try first [ reflexivity | assumption | lia ].
Qed.

Lemma string_eq_refl (s : string) : string_eq s s.
Proof.
  apply string_eq_ext.
  split; [|intros]; reflexivity.
Qed.

Lemma string_eq_spec (s1 s2 : string) : string_eq s1 s2 <-> s1 = s2.
Proof. split; [apply string_eq_correct|intros []; apply string_eq_refl]. Qed.

Lemma string_lt_gt (s1 s2 : string) : string_lt s1 s2 <-> string_gt s2 s1.
Proof.
  unfold string_lt, string_gt.
  rewrite !compare_spec.
  setoid_rewrite Uint63.compare_def_spec; unfold compare_def.
  split; intros [i (H1 & H2 & Hprefix & H)]; exists i.
  all: repeat case_if; inversion H; try lia.
  all: repeat split; [assumption|assumption|].
  all: intros; symmetry; apply Hprefix; assumption.
Qed.

Lemma string_lt_spec (s1 s2 : string) :
  string_lt s1 s2 <->
    exists i,
      (i <=? length s1 = true)%uint63 /\
        (i <=? length s2 = true)%uint63 /\
        (forall j, (j <? i = true)%uint63 -> get s1 j = get s2 j) /\
        ((i = length s1 /\ (i <? length s2 = true)%uint63) \/
           (i <? length s1 = true /\
              i <? length s2 = true /\
              get s1 i <? get s2 i = true)%uint63).
Proof.
  unfold string_lt. rewrite compare_spec.
  setoid_rewrite Uint63.compare_def_spec; unfold compare_def.
  split.
  - intros [i (H1 & H2 & Hget & Heq)]; exists i.
    repeat split; [assumption..|].
    repeat case_if; try inversion Heq.
    + left. split; lia.
    + right. repeat split; lia.
  - intros [i (H1 & H2 & Hget & H)]; exists i.
    repeat split; [assumption..|].
    destruct H as [(-> & Hi)|(Hi1 & Hi2 & H)].
    + repeat case_if; try reflexivity; lia.
    + repeat case_if; try reflexivity; lia.
Qed.

Lemma compare_trans (c : comparison) (s1 s2 s3 : string) :
  compare s1 s2 = c -> compare s2 s3 = c -> compare s1 s3 = c.
Proof.
  rewrite !compare_spec.
  setoid_rewrite Uint63.compare_def_spec; unfold compare_def.
  intros [i1 (Hi1s1&Hi1s2&Hi1&H1)] [i2 (Hi2s2&Hi2s3&Hi2&H2)].
  destruct (i1 <? i2)%uint63 eqn:Hlt; [exists i1 | exists i2]; repeat split; try lia.
  - intros j Hji1.
    assert ((j <? i2)%uint63 = true) as Hji2 by lia.
    pose proof (Hi1 j Hji1) as Hj1.
    pose proof (Hi2 j Hji2) as Hj2.
    revert Hj1 Hj2. intros -> <-. reflexivity.
  - clear H2; revert H1.
    assert (get s2 i1 = get s3 i1) as Hs2s3. { apply Hi2. assumption. }
    repeat case_if; intros H1; try assumption; try lia; try subst c.
  - intros j Hji2.
    assert ((j <? i1)%uint63 = true) as Hji1 by lia.
    pose proof (Hi1 j Hji1) as Hj1.
    pose proof (Hi2 j Hji2) as Hj2.
    revert Hj1 Hj2. intros -> <-. reflexivity.
  - destruct (i1 =? i2)%uint63 eqn:Heqi1i2.
    + apply eqb_spec in Heqi1i2. subst i2. revert H1 H2.
      repeat case_if.
      all: intros H1; try rewrite H1; try inversion H1.
      all: intros H2; try rewrite H2; try inversion H2.
      all: try reflexivity; lia.
    + clear H1; revert H2.
      assert (get s1 i2 = get s2 i2) as Hs1s2. { apply Hi1. lia. }
      repeat case_if; intros H1; try assumption; try lia; try subst c.
Qed.

Lemma string_eq_trans (s1 s2 s3 : string) :
  string_eq s1 s2 -> string_eq s2 s3 -> string_eq s1 s3.
Proof. apply compare_trans. Qed.

Lemma string_lt_trans (s1 s2 s3 : string) :
  string_lt s1 s2 -> string_lt s2 s3 -> string_lt s1 s3.
Proof. apply compare_trans. Qed.

Lemma string_gt_trans (s1 s2 s3 : string) :
  string_gt s1 s2 -> string_gt s2 s3 -> string_gt s1 s3.
Proof. apply compare_trans. Qed.

Lemma string_le_trans (s1 s2 s3 : string) :
  string_le s1 s2 -> string_le s2 s3 -> string_le s1 s3.
Proof.
  unfold string_le, string_gt.
  intros H1 H2 H3.
  destruct (compare s1 s2) eqn:Hc1;
  destruct (compare s2 s3) eqn:Hc2.
  all: try lazymatch goal with H : ~ ?c = ?c |- _ => apply H; reflexivity end.
  - pose proof (compare_trans _ _ _ _ Hc1 Hc2) as Htrans.
    rewrite Htrans in H3; inversion H3.
  - apply string_eq_correct in Hc1; subst s1.
    rewrite Hc2 in H3; inversion H3.
  - apply string_eq_correct in Hc2; subst s3.
    rewrite Hc1 in H3; inversion H3.
  - pose proof (compare_trans _ _ _ _ Hc1 Hc2) as Htrans.
    rewrite Htrans in H3; inversion H3.
Qed.

Lemma string_ge_trans  (s1 s2 s3 : string) :
  string_ge s1 s2 -> string_ge s2 s3 -> string_ge s1 s3.
Proof.
  unfold string_ge, string_lt.
  intros H1 H2 H3.
  destruct (compare s1 s2) eqn:Hc1;
  destruct (compare s2 s3) eqn:Hc2.
  all: try lazymatch goal with H : ~ ?c = ?c |- _ => apply H; reflexivity end.
  - pose proof (compare_trans _ _ _ _ Hc1 Hc2) as Htrans.
    rewrite Htrans in H3; inversion H3.
  - apply string_eq_correct in Hc1; subst s1.
    rewrite Hc2 in H3; inversion H3.
  - apply string_eq_correct in Hc2; subst s3.
    rewrite Hc1 in H3; inversion H3.
  - pose proof (compare_trans _ _ _ _ Hc1 Hc2) as Htrans.
    rewrite Htrans in H3; inversion H3.
Qed.

(** * Conversion to / from lists *)

Fixpoint to_list_aux (s : string) (off : int) (len : nat) : list char63 :=
  match len with
  | O     => nil
  | S len => cons (get s off) (to_list_aux s (off + 1)%uint63 len)
  end.
Definition to_list (s : string) : list char63 :=
  let len := Z.to_nat (to_Z (length s)) in
  to_list_aux s 0%uint63 len.
Arguments to_list _%_pstring.

Fixpoint of_list (cs : list char63) : string :=
  match cs with
  | nil       => empty
  | cons c cs => cat (make 1 c) (of_list cs)
  end.

Lemma length_0_empty (s : string) : length s = 0%uint63 -> s = ""%pstring.
Proof.
  intros Heq. apply string_eq_spec, string_eq_ext.
  split; [assumption|lia].
Qed.

Lemma sub_cat (s : string) (len : int) :
  (len <=? length s = true)%uint63 ->
  s = cat (sub s 0%uint63 len) (sub s len (length s - len)%uint63).
Proof.
  intros Hlen. apply string_eq_correct. apply string_eq_ext.
  assert (range_valid s 0 len) as H1.
  { unfold range_valid. ring_simplify (length s - 0)%uint63. lia. }
  assert (range_valid s len (length s - len)) as H2.
  { unfold range_valid. lia. }
  assert (len + (length s - len) = length s)%uint63 as Heq by ring.
  split.
  - rewrite cat_length_spec, !sub_length_spec; try assumption.
    + ring.
    + rewrite !sub_length_spec; try assumption.
      unfold length_valid. rewrite Heq.
      apply valid_length.
 - intros i Hi.
   destruct (i <? len)%uint63 eqn:Hleni.
   + rewrite cat_get_spec_l, sub_get_spec; try assumption.
     { ring_simplify (0 + i)%uint63. reflexivity. }
     { rewrite !sub_length_spec, Heq; try assumption. apply valid_length. }
     { rewrite sub_length_spec; assumption. }
   + rewrite cat_get_spec_r.
     { rewrite !sub_length_spec; [|assumption].
       rewrite sub_get_spec; [f_equal; ring|assumption|].
       revert Hi. rewrite !ltb_spec, !sub_spec.
       rewrite !Z.mod_small; lia. }
     { rewrite !sub_length_spec, Heq; try assumption. apply valid_length. }
     { rewrite !sub_length_spec; assumption. }
     { rewrite !sub_length_spec, Heq; try assumption. }
Qed.

Lemma sub_sub (s : string) (off1 len1 off2 len2 : int) :
  range_valid s off1 len1 ->
  range_valid (sub s off1 len1) off2 len2 ->
  sub (sub s off1 len1) off2 len2 = sub s (off1 + off2)%uint63 len2.
Proof.
  intros Hr1 Hr2.
  assert (range_valid s (off1 + off2)%uint63 len2) as Hr3.
  { unfold range_valid in Hr1, Hr2 |- *.
    rewrite sub_length_spec in Hr2; [|assumption].
    destruct Hr1 as [Hr11 Hr12]. destruct Hr2 as [Hr21 Hr22].
    rewrite !leb_spec, !add_spec, !sub_spec, !add_spec in *.
    rewrite Z.mod_small in Hr12; [|lia].
    rewrite Z.mod_small in Hr22; [|lia].
    rewrite Z.mod_small; [|lia].
    rewrite Z.mod_small; [|lia]. lia. }
  apply string_eq_correct. apply string_eq_ext. split.
  - rewrite !sub_length_spec; [reflexivity|assumption|assumption].
  - intros i. rewrite sub_length_spec; [|assumption]. intros Hi.
    assert (off2 + i <? len1 = true)%uint63.
    { unfold range_valid in Hr1, Hr2 |- *.
      rewrite sub_length_spec in Hr2; [|assumption].
      destruct Hr1 as [Hr11 Hr12].
      destruct Hr2 as [Hr21 Hr22].
      destruct Hr3 as [Hr31 Hr32].
      rewrite !leb_spec, ltb_spec, !add_spec, !sub_spec, !add_spec in *.
      rewrite Z.mod_small in Hr12; [|lia].
      rewrite Z.mod_small in Hr22; [|lia].
      rewrite Z.mod_small in Hr31; [|lia].
      rewrite !Z.mod_small in Hr32; try lia.
      2: { rewrite Z.mod_small; [|lia]. lia. }
      rewrite Z.mod_small; [|lia]. lia. }
    rewrite !sub_get_spec; try assumption. f_equal. ring.
Qed.

Definition of_nat (n : nat) : int := of_Z (Z.of_nat n).

Lemma of_nat_S (n : nat) :
  (Z.of_nat n + 1 < wB)%Z ->
  of_nat (S n) = (1 + of_nat n)%uint63.
Proof.
  unfold of_nat; rewrite Nat2Z.inj_succ; unfold Z.succ; fold (of_nat n).
  intros H. rewrite add_comm.
  assert (Z.of_nat n + 1 = (to_Z (of_nat n) + to_Z 1) mod wB)%Z as ->.
  2: rewrite <-add_spec, of_to_Z; reflexivity.
  unfold of_nat. rewrite of_Z_spec.
  assert (to_Z 1 = 1%Z) as -> by reflexivity.
  rewrite !Z.mod_small; [lia|lia|].
  rewrite Z.mod_small; lia.
Qed.

Lemma to_Z_of_nat (n : nat) :
  (Z.of_nat n < wB)%Z ->
  to_Z (of_nat n) = Z.of_nat n.
Proof.
  intros H. unfold of_nat. rewrite of_Z_spec.
  rewrite Z.mod_small; lia.
Qed.

Lemma range_valid_length (s : string) (off len : int) :
  range_valid s (length s) len -> len = 0%uint63.
Proof.
  intros [Hr1 Hr2].
  ring_simplify (length s - length s)%uint63 in Hr2. lia.
Qed.

Lemma range_valid_full (s : string) : range_valid s 0 (length s).
Proof.
  unfold range_valid. ring_simplify (length s - 0)%uint63. lia.
Qed.

Lemma range_valid_shift (s : string) (off len n : int) :
  to_Z (len + n) = (φ (len)%uint63 + φ (n)%uint63)%Z ->
  range_valid s off (len + n) ->
  range_valid s (off + n) len.
Proof.
  intros Hlenn [Hr1 Hr2].
  rewrite leb_spec, add_spec, sub_spec in Hr2.
  rewrite (Z.mod_small (to_Z (length s) - φ (off)%uint63)%Z) in Hr2; [|lia].
  assert (φ (len)%uint63 + φ (n)%uint63 < wB)%Z as Hlt.
  { rewrite <-Hlenn. pose proof (Uint63.to_Z_bounded (len + n)). lia. }
  rewrite Z.mod_small in Hr2; [|lia].
  unfold range_valid.
  rewrite !leb_spec, sub_spec, add_spec, !Z.mod_small; lia.
Qed.

Lemma of_to_list_aux (s : string) (off : int) (len : nat) :
  (Z.of_nat len < wB)%Z ->
  range_valid s off (of_nat len) ->
  of_list (to_list_aux s off len) = sub s off (of_nat len).
Proof.
  revert off s; induction len as [|len IH]; intros off s Hlen Hrange; simpl.
  - pose proof (sub_length_spec s off 0 Hrange).
    symmetry. apply length_0_empty. assumption.
  - assert (1 <=? of_nat (S len) = true)%uint63.
    { rewrite of_nat_S, leb_spec, add_spec, to_Z_of_nat, Z.mod_small; lia. }
    rewrite (sub_cat (sub s off (of_nat (S len))) 1%uint63).
    2: { rewrite sub_length_spec; [lia|assumption]. }
    f_equal.
    { destruct Hrange as [Hr1 Hr2].
      rewrite sub_sub; ring_simplify (off + 0)%uint63.
      2: split; assumption.
      2: { split; [lia|].
           ring_simplify (length (sub s off (of_nat (S len))) - 0)%uint63.
           rewrite sub_length_spec; [|split;assumption]. lia. }
      apply string_eq_correct. apply string_eq_ext. split.
      * rewrite make_length_spec; [|unfold length_valid, max_length; lia].
        rewrite sub_length_spec; [reflexivity|split; lia].
      * intros i Hi.
        assert (length_valid 1) as Hvalid.
        { unfold length_valid, max_length. lia. }
        rewrite make_length_spec in Hi; [|assumption].
        assert (i = 0%uint63) as -> by lia.
        rewrite sub_get_spec; [|split; lia|lia].
        ring_simplify (off + 0)%uint63.
        rewrite make_get_spec_valid; [reflexivity|assumption| |lia].
        apply get_valid. destruct (off =? length s)%uint63 eqn:Hlt; [|lia].
        exfalso. apply eqb_correct in Hlt. rewrite Hlt in Hr2.
        ring_simplify (length s - length s)%uint63 in Hr2. lia. }
    rewrite sub_length_spec; [|assumption].
    rewrite of_nat_S in * |- *; try lia.
    assert (range_valid s (off + 1) (of_nat len))%uint63 as Hr.
    { apply range_valid_shift.
      - rewrite add_spec, Z.mod_small; [reflexivity|]. split; [lia|].
        assert (to_Z 1 = 1%Z) as -> by reflexivity.
        rewrite Nat2Z.inj_succ in Hlen.
        unfold of_nat. rewrite of_Z_spec, Z.mod_small; lia.
      - assert (of_nat len + 1 = 1 + of_nat len)%uint63 as -> by ring.
        assumption. }
    ring_simplify (1 + of_nat len - 1)%uint63.
    rewrite sub_sub.
    2: assumption.
    2: { unfold range_valid.
         rewrite sub_length_spec; [|assumption].
         ring_simplify (1 + of_nat len - 1)%uint63. lia. }
    apply IH; [lia|assumption].
Qed.

Lemma sub_full (s : string) :
  sub s 0%uint63 (length s) = s.
Proof.
  apply string_eq_correct. apply string_eq_ext.
  pose proof (range_valid_full s) as Hr.
  split; [rewrite sub_length_spec; [reflexivity|assumption]|].
  intros i.
  rewrite sub_length_spec; [|assumption].
  intros Hi.
  rewrite sub_get_spec; [|assumption|assumption].
  ring_simplify (0 + i)%uint63. reflexivity.
Qed.

Lemma of_to_list (s : string) : of_list (to_list s) = s.
Proof.
  unfold to_list.
  assert (of_nat (Z.to_nat (to_Z (length s))) = length s)%uint63 as Heq.
  { unfold of_nat. rewrite Z2Nat.id; [|lia]. rewrite of_to_Z. reflexivity. }
  rewrite of_to_list_aux, Heq; [apply sub_full|lia|].
  unfold range_valid.
  ring_simplify (length s - 0)%uint63. lia.
Qed.

Lemma to_of_list (l : list char63) :
  (of_nat (List.length l) <=? max_length = true)%uint63 ->
  to_list (of_list l) = l.
Proof.
Admitted.

Require Import OrderedType.

Module OT <: OrderedType.OrderedType with Definition t := string.
  Definition t := string.

  Definition eq := string_eq.
  Definition lt := string_lt.

  Lemma eq_refl (s : t) : eq s s.
  Proof. apply string_eq_refl. Qed.

  Lemma eq_sym (s1 s2 : t) : eq s1 s2 -> eq s2 s1.
  Proof. unfold eq. rewrite !string_eq_spec. apply eq_sym. Qed.

  Lemma eq_trans (s1 s2 s3 : t) : eq s1 s2 -> eq s2 s3 -> eq s1 s3.
  Proof. unfold eq. rewrite !string_eq_spec. apply eq_trans. Qed.

  Lemma lt_trans (s1 s2 s3 : t) : lt s1 s2 -> lt s2 s3 -> lt s1 s3.
  Proof. unfold lt. apply string_lt_trans. Qed.

  Lemma lt_not_eq (s1 s2 : t) : lt s1 s2 -> not (eq s1 s2).
  Proof. unfold lt, string_lt, eq, string_eq. intros ->. discriminate. Qed.

  #[program]
  Definition compare (s1 s2 : t) : Compare lt eq s1 s2 :=
    match compare s1 s2 with
    | Eq => EQ _
    | Lt => LT _
    | Gt => GT _
    end.
  Next Obligation.
    unfold eq, string_eq. symmetry. assumption.
  Defined.
  Next Obligation.
    unfold lt, string_lt. symmetry. assumption.
  Defined.
  Next Obligation.
    apply string_lt_gt. unfold lt, string_lt. symmetry. assumption.
  Defined.

  Hint Immediate eq_sym : core.
  Hint Resolve eq_refl eq_trans lt_not_eq lt_trans : core.

  Definition eq_dec (s1 s2 : t) : {eq s1 s2} + {~ eq s1 s2}.
  Proof.
    unfold eq, string_eq.
    destruct (PrimString.compare s1 s2).
    - left. reflexivity.
    - right. discriminate.
    - right. discriminate.
  Qed.
End OT.

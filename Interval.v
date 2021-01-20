Set Implicit Arguments.

Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.

Require Import Coq.Arith.Arith.
Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Decidable.

Module Type Lt := Typ <+ HasLt.
Module Type HasLtDec (Import E : Lt).
  Parameter lt_dec : forall x y : t, {lt x y} + {~ lt x y}.
End HasLtDec.

Module Type Le := Typ <+ HasLe.
Module Type HasLeDec (Import E : Le).
  Parameter le_dec : forall x y : t, {le x y} + {~ le x y}.
End HasLeDec.

Module Type IsPartialOrder (Import E:EqLe).
  Declare Instance le_preorder : PreOrder le.
  Declare Instance le_compat : Proper (eq==>eq==>iff) le.
End IsPartialOrder.
Module Type PartialOrder := EqualityType <+ HasLe <+ IsPartialOrder.

Module Type IntervalType.
  Include EqLtLe.
  Include IsEq <+ IsStrOrder <+ IsPartialOrder.
  Include HasEqDec <+ HasLtDec <+ HasLeDec.
  Include LeIsLtEq.

  Include HasBoolOrdFuns.
  Include BoolOrdSpecs.
End IntervalType.

Module Interval <: IntervalType.
  Import PeanoNat Peano_dec Compare_dec.

  Arguments Nat.le_trans [n] [m] [p].
  Arguments leb_complete [m] [n].

  Definition t : Type :=
    {(left, right) : nat * nat | left <= right}.

  Program Definition left_endpoint (self : t) : nat :=
    fst self.

  Program Definition right_endpoint (self : t) : nat :=
    snd self.

  Definition ok (self : t) : left_endpoint self <= right_endpoint self :=
    let 'exist _ (_, _) x_le_y := self in x_le_y.

  Include HasUsualEq.
  Include UsualIsEq.

  Lemma eq_spec : forall self other : t,
    eq self other <->
    left_endpoint self = left_endpoint other /\
    right_endpoint self = right_endpoint other.
  Proof.
    intros self other.
    destruct self as [(self_left & self_right) self_ok], other as [(other_left & other_right) other_ok]; simpl.
    unfold left_endpoint, right_endpoint; simpl. (* TODO *)
    split.
      now inversion 1.
    intros [eq_left eq_right].
    revert self_ok.
    rewrite eq_left, eq_right; intros self_le.
    now rewrite le_unique with (le_mn1 := self_le) (le_mn2 := other_ok).
  Qed.

  Definition eqb (self other : t) : bool :=
    ((left_endpoint self =? left_endpoint other) && (right_endpoint self =? right_endpoint other)) %bool.

  Lemma eqb_eq : forall self other : t, eqb self other = true <-> eq self other.
  Proof.
    intros self other.
    symmetry.
    unfold eqb, eq; rewrite Bool.andb_true_iff, ?PeanoNat.Nat.eqb_eq.
    apply eq_spec.
  Qed.
  Include HasEqBool2Dec.

  Definition ltb (self other : t) :=
    right_endpoint self <? left_endpoint other.
  Definition lt (self other : t) : Prop := right_endpoint self < left_endpoint other.
  Lemma ltb_lt : forall self other, ltb self other = true <-> lt self other.
  Proof.
    intros self other.
    now unfold ltb; rewrite Nat.ltb_lt.
  Qed.
  Definition lt_dec : forall x y : t, {lt x y} + {~ lt x y}.
  Proof.
    intros x y.
    destruct (ltb x y) eqn: H; [left| right].
      now apply ltb_lt.
    rewrite <- ltb_lt.
    now rewrite Bool.not_true_iff_false.
  Defined.

  Definition leb (self other : t) :=
    ((ltb self other) || (eqb self other))%bool.
  Definition le (self other : t) : Prop := lt self other \/ eq self other.
  Lemma leb_le : forall self other, leb self other = true <-> le self other.
  Proof.
    intros self other.
    unfold leb.
    now rewrite Bool.orb_true_iff, eqb_eq, ltb_lt.
  Qed.
  Definition le_dec : forall x y : t, {le x y} + {~ le x y}.
  Proof.
    intros x y.
    destruct (eq_dec x y) as [x_eq_y| x_neq_y].
      now left; right.
    destruct (lt_dec x y) as [x_lt_y| x_nlt_y].
      now left; left.
    right.
    now intros [x_eq_y| x_lt_y].
  Defined.

  Instance lt_strorder : StrictOrder lt.
  Proof.
    split.
      intros [(self_left & self_right) self_le].
      change (~ self_right < self_left).
      now apply Nat.nlt_ge.
    intros [(x_left & x_right) x_le] [(y_left & y_right) y_le] [(z_left & z_right) z_le].
    unfold lt; simpl.
    intros x_lt_y y_lt_z.
    rewrite x_lt_y.
    now apply Nat.le_lt_trans with y_right.
  Qed.
  Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    intros x₁ x₂ -> y₁ y₂ ->.
    reflexivity.
  Qed.

  Instance le_preorder : PreOrder le :=
    StrictOrder_PreOrder _ _ _.
  Instance le_partialorder : PartialOrder eq le :=
    StrictOrder_PartialOrder _ _ _.
  Instance le_compat : Proper (eq ==> eq ==> iff) le :=
    PartialOrder_proper le_partialorder.

  Lemma le_lteq : forall self other : t, le self other <-> lt self other \/ eq self other.
  Proof.
    reflexivity.
  Qed.

  Program Definition new (x : nat) (y : nat | x <= y) : t :=
    (x, y).

  Program Definition replace_left_endpoint (self : t) (x : nat | x <= left_endpoint self) : t * {left : nat | left = left_endpoint self} :=
    ((x, right_endpoint self), left_endpoint self).
  Next Obligation.
    pose (ok self).
    now transitivity (left_endpoint self).
  Defined.

  Program Definition replace_right_endpoint (self : t) (y : nat | right_endpoint self <= y) : t * {right : nat | right = right_endpoint self} :=
    ((left_endpoint self, y), right_endpoint self).
  Next Obligation.
    pose (ok self).
    now transitivity (right_endpoint self).
  Defined.

  Definition In : nat -> t -> Prop :=
    fun n interval => left_endpoint interval <= n <= right_endpoint interval.

  Add Parametric Morphism : In with signature Logic.eq ==> eq ==> iff as In_compat.
  Proof.
    intros n self other eq.
    unfold In.
    now apply eq_spec in eq as (-> & ->).
  Qed.

  Lemma In_left_endpoint : forall self : t, In (left_endpoint self) self.
  Proof.
    firstorder using ok.
  Qed.

  Lemma In_right_endpoint : forall self : t, In (right_endpoint self) self.
  Proof.
    firstorder using ok.
  Qed.

  Lemma eq_iff_In : forall self other : t, eq self other <-> (forall n : nat, In n self <-> In n other).
  Proof.
    intros self other.
    rewrite eq_spec.
    split.
      unfold In.
      now intros [-> ->] n.
    intros In_iff.
    assert (In_left_self : In (left_endpoint other) self) by apply In_iff, In_left_endpoint.
    assert (In_right_self : In (right_endpoint other) self) by apply In_iff, In_right_endpoint.
    assert (In_left_other : In (left_endpoint self) other) by apply In_iff, In_left_endpoint.
    assert (In_right_other : In (right_endpoint self) other) by apply In_iff, In_right_endpoint.
    split; apply Nat.le_antisymm; firstorder.
  Qed.

  Lemma not_In_iff : forall (n : nat) (interval : t), ~ In n interval <-> left_endpoint interval > n \/ n > right_endpoint interval.
  Proof.
    intros n interval.
    unfold In, gt.
    rewrite ?Nat.lt_nge.
    split; intros H.
      apply not_and in H.
        assumption.
      unfold decidable.
      destruct (Compare_dec.le_dec (left_endpoint interval) n) as [?| ?]; [left| right]; assumption.
    destruct H as [H| H]; easy.
  Qed.

  Definition In_dec : forall (n : nat) (interval : t), {In n interval} + {~ In n interval}.
  Proof.
    intros n interval.
    destruct (le_lt_dec (left_endpoint interval) n) as [left_le_n| left_gt_n].
      destruct (le_lt_dec n (right_endpoint interval)) as [n_le_right| n_gt_right].
        now left.
      right; firstorder.
      apply not_In_iff.
      firstorder.
    right; apply not_In_iff.
    firstorder.
  Defined.

  Program Definition contains (self : t) (n : nat) : {b : bool | In n self <-> b = true} :=
    ((left_endpoint self <=? n) && (n <=? right_endpoint self)).
  Next Obligation.
    unfold In.
    now rewrite Bool.andb_true_iff, ?Nat.leb_le.
  Defined.

  Lemma and_In_iff : forall self other n, In n self /\ In n other <-> max (left_endpoint self) (left_endpoint other) <= n <= min (right_endpoint self) (right_endpoint other).
  Proof.
    intros self other n.
    unfold In.
    rewrite Nat.max_lub_iff, ?Nat.min_glb_iff.
    firstorder.
  Qed.

  Lemma intersection_test : forall self other : t, BoolSpec
    (max (left_endpoint self) (left_endpoint other) <= min (right_endpoint self) (right_endpoint other))
    (max (left_endpoint self) (left_endpoint other) > min (right_endpoint self) (right_endpoint other))
    (negb (ltb self other) && negb (ltb other self)).
  Proof.
    intros self other.
    assert (true_gt : negb (ltb self other) && negb (ltb other self) = false <-> max (left_endpoint self) (left_endpoint other) > min (right_endpoint self) (right_endpoint other)).
      pose (Ok_self := ok self).
      pose (Ok_other := ok other).
      rewrite <- negb_orb, negb_false_iff, orb_true_iff, ?ltb_lt.
      unfold gt.
      rewrite Nat.max_lt_iff, 2!Nat.min_lt_iff.
      firstorder.
        absurd (left_endpoint self < left_endpoint self).
          apply Nat.lt_irrefl.
        now apply Nat.le_lt_trans with (right_endpoint self).
      absurd (right_endpoint other < right_endpoint other).
        apply Nat.lt_irrefl.
      now apply Nat.lt_le_trans with (left_endpoint other).
    assert (false_le : negb (ltb self other) && negb (ltb other self) = true <-> max (left_endpoint self) (left_endpoint other) <= min (right_endpoint self) (right_endpoint other)).
      rewrite Nat.le_ngt, <- not_false_iff_true.
      firstorder.
    destruct (negb (ltb self other) && negb (ltb other self)) eqn: e; [left| right].
      now apply false_le.
    now apply true_gt.
  Qed.

  Inductive OptionSpec (A : Type) (P : A -> Prop) (Q : Prop) : option A -> Prop :=
  | OptionSpecSome : forall a : A, P a -> OptionSpec P Q (Some a)
  | OptionSpecNone : Q -> OptionSpec P Q None.

  Lemma BoolSpec_true : forall (P Q : Prop) (b : bool), b = true -> BoolSpec P Q b -> P.
    intros P Q b ->.
    now inversion 1.
  Qed.

  Lemma BoolSpec_false : forall (P Q : Prop) (b : bool), b = false -> BoolSpec P Q b -> Q.
    intros P Q b ->.
    now inversion 1.
  Qed.

  Definition  intersection_spec (self other : t) : option (nat * nat) -> Prop := OptionSpec
    (fun interval : nat * nat => let (left, right) := interval in left <= right /\ forall n : nat, left <= n <= right <-> In n self /\ In n other)
    (forall n : nat, ~ In n self \/ ~ In n other).

  Program Definition intersection (self other : t) : {interval : option (nat * nat) | intersection_spec self other interval} :=
    if dec (negb (ltb self other) && negb (ltb other self))%bool then
    Some (max (left_endpoint self) (left_endpoint other), min (right_endpoint self) (right_endpoint other)) else
    None.
  Next Obligation.
    pose (Ok_self := ok self).
    pose (Ok_other := ok other).
    assert (Nat.max (left_endpoint self) (left_endpoint other) <= Nat.min (right_endpoint self) (right_endpoint other)).
      now eapply BoolSpec_true, intersection_test.
    constructor.
    split.
      assumption.
    intros n.
    now rewrite and_In_iff.
  Defined.
  Next Obligation.
    constructor.
    intros n.
    assert (Nat.max (left_endpoint self) (left_endpoint other) > Nat.min (right_endpoint self) (right_endpoint other)).
      now eapply BoolSpec_false, intersection_test.
    enough (~ (In n self /\ In n other)).
      firstorder using In_dec.
    rewrite and_In_iff.
    apply Nat.nle_gt in H; contradict H.
    now transitivity n.
  Defined.
End Interval.

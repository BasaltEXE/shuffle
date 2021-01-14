Set Implicit Arguments.

Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.

Require MSetInterface OrdersFacts OrdersLists.
Require Coq.MSets.MSetFacts Coq.MSets.MSetProperties.
Require Coq.FSets.FMapInterface Coq.FSets.FMapFacts.

Require Import Coq.Classes.RelationClasses.

Require Import Coq.Logic.Decidable.

Require Import Coq.Bool.Bool.


Require Coq.Arith.PeanoNat Coq.Arith.Peano_dec.

Require Coq.Logic.Decidable.


Require Coq.Structures.Orders Coq.Structures.OrdersFacts Coq.Structures.OrdersTac.

Require Coq.Structures.Equalities Coq.Structures.EqualitiesFacts.
Require Coq.Structures.Orders Coq.Structures.OrdersAlt Coq.Structures.OrdersFacts.

Require Import  Coq.Classes.Morphisms_Prop.

Import ListNotations.

Import Coq.Structures.Equalities Coq.Structures.EqualitiesFacts.
Import Coq.Structures.Orders Coq.Structures.OrdersAlt Coq.Structures.OrdersFacts.

Require Import FunInd.

Module Card (Key Owner : DecidableType) <: DecidableType.
  Inductive Card : Type :=
  | Talon : Key.t -> Card
  | Assigned : Owner.t -> Card.

  Definition t := Card.

  Definition eq : t -> t -> Prop :=
    fun self other =>
    match self, other with
    | Talon self_key, Talon other_key => Key.eq self_key other_key
    | Assigned self_owner, Assigned other_owner => Owner.eq self_owner other_owner
    | _, _ => False
    end.

  Definition eq_talon_ind : forall (key : Key.t) (P : forall y : t, eq (Talon key) y -> Prop), (forall (y_key : Key.t) (x_eq_y : Key.eq key y_key), P (Talon y_key) x_eq_y) -> forall (y : t) (x_eq_y : eq (Talon key) y), P y x_eq_y.
  Proof.
    intros key P IHP [y_key| y_owner].
      apply IHP.
    contradiction.
  Defined.

  Definition eq_assigned_ind : forall (x_owner : Owner.t) (P : forall y : t, eq (Assigned x_owner) y -> Prop), (forall (y_owner : Owner.t) (x_eq_y : Owner.eq x_owner y_owner), P (Assigned y_owner) x_eq_y) -> forall (y : t) (x_eq_y : eq (Assigned x_owner) y), P y x_eq_y.
  Proof.
    intros x_owner P IHP [y_key| y_owner].
      contradiction.
    apply IHP.
  Defined.

  Instance eq_equiv : Equivalence eq.
  Proof.
    split.
        intros card.
        destruct card as [key| owner]; simpl; reflexivity.
      intros [x_key| x_owner] [y_key| y_owner] x_eq_y; now simpl.
    intros [x_key| x_owner] y z x_eq_y y_eq_z.
      induction x_eq_y as [y_key x_eq_y] using eq_talon_ind.
      induction y_eq_z as [z_key y_eq_z] using eq_talon_ind.
      simpl.
      now transitivity y_key.
    induction x_eq_y as [y_key x_eq_y] using eq_assigned_ind.
    induction y_eq_z as [z_key y_eq_z] using eq_assigned_ind.
    simpl.
    now transitivity y_key.
  Defined.

  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    intros x y.
    destruct x as [x_key| x_owner], y as [y_key| y_owner].
          apply Key.eq_dec.
        now right.
      now right.
    apply Owner.eq_dec.
  Defined.
End Card.

Module Option (E : DecidableType) <: DecidableType.
  Definition t : Type := option E.t.

  Definition eq : t -> t -> Prop :=
    fun self other =>
      match self, other with
      | Some self_some, Some other_some => E.eq self_some other_some
      | None, None => True
      | _, _ => False
      end.

  Definition eq_None_ind : forall P : forall other : t, eq None other -> Prop, P None I -> forall (other : t) (self_eq_other : eq None other), P other self_eq_other.
  Proof.
    intros P P_None other self_eq_other.
    destruct other as [other_some|].
      contradiction.
    now destruct self_eq_other.
  Defined.

  Definition eq_Some_ind : forall (self : E.t) (P : forall other : t, eq (Some self) other -> Prop), (forall (other : E.t) (self_eq_other : E.eq self other), P (Some other) self_eq_other) -> forall (other : t) (self_eq_other : eq (Some self) other), P other self_eq_other.
Proof.
    intros self P P_Some other self_eq_other.
    destruct other as [other_some|].
      now apply P_Some.
    contradiction.
  Defined.

  Instance eq_equiv : Equivalence eq.
  Proof.
    split.
        intros [x|]; simpl; reflexivity.
      intros [x|] y x_eq_y.
        induction x_eq_y as [y x_eq_y] using eq_Some_ind.
        now simpl; symmetry.
      now induction y, x_eq_y using eq_None_ind.
    intros [x|] y z x_eq_y y_eq_z.
      induction x_eq_y as [y x_eq_y] using eq_Some_ind.
      induction y_eq_z as [z y_eq_z] using eq_Some_ind.
      simpl.
      now transitivity y.
    induction y, x_eq_y using eq_None_ind.
    induction z, y_eq_z using eq_None_ind.
    easy.
  Qed.

  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    intros [x|] [y|].
          apply E.eq_dec.
        now right.
      now right.
    now left.
  Defined.
End Option.

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
Print Module Type IntervalType.

  Definition IsSome : forall A : Type, (A -> Prop) -> option A -> Prop :=
    fun A P x =>
      match x with
      | Some x' => P x'
      | _ => False
      end.

  Definition IsNone : forall A : Type, option A -> Prop :=
    fun A x =>
      match x with
      | Some _ => False
      | _ => True
      end.

Module Interval' <: IntervalType.
  Import PeanoNat Peano_dec Compare_dec.

  Arguments Nat.le_trans [n] [m] [p].
  Arguments leb_complete [m] [n].

  Inductive Interval : Type :=
  | intro : forall left right : nat, left <= right -> Interval.

  Definition t : Type := Interval.

  Definition left_endpoint (self : t) : nat :=
    let (left, right, _) := self in left.

  Definition right_endpoint (self : t) : nat :=
    let (left, right, _) := self in right.

  Include HasUsualEq.
  Include UsualIsEq.

  Definition eqb (self other : t) : bool :=
    ((left_endpoint self =? left_endpoint other) && (right_endpoint self =? right_endpoint other)) %bool.

  Definition eqb_eq : forall self other : t, eqb self other = true <-> eq self other.
  Proof.
    intros self other.
    unfold eqb, eq; rewrite Bool.andb_true_iff, ?PeanoNat.Nat.eqb_eq.
    destruct self as [self_left self_right self_le], other as [other_left other_right other_le]; simpl.
    split.
      intros [eq_left eq_right].
      revert self_le.
      rewrite eq_left, eq_right; intros self_le.
      now rewrite le_unique with (le_mn1 := self_le) (le_mn2 := other_le).
    now inversion 1.
  Defined.
  Include HasEqBool2Dec.

  Definition ltb (self other : t) :=
    right_endpoint self <? left_endpoint other.
  Definition lt (self other : t) : Prop := right_endpoint self < left_endpoint other.
  Definition ltb_lt : forall self other, ltb self other = true <-> lt self other.
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
  Definition leb_le : forall self other, leb self other = true <-> le self other.
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
      intros [self_left self_right self_le].
      change (~ self_right < self_left).
      now apply Nat.nlt_ge.
    intros [x_left x_right x_le] [y_left y_right y_le] [z_left z_right z_le].
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

  Definition le_lteq : forall self other : t, le self other <-> lt self other \/ eq self other.
  Proof.
    reflexivity.
  Qed.

  Definition Is : nat -> nat -> t -> Prop :=
    fun left right interval => left_endpoint interval = left /\ right_endpoint interval = right.

  Definition new (x y : nat) : option t :=
    match x <=? y as b return (x <=? y = b -> option t) with
    | true  => fun x_le_y => Some (intro (leb_complete x_le_y))
    | false => fun x_nle_y => None
    end eq_refl.

  Definition new_spec_le : forall x y : nat, x <= y -> IsSome (Is x y) (new x y).
  Proof.
    intros x y x_le_y.
    unfold new; simpl in *.
    generalize (@leb_complete x y).
    now rewrite leb_correct with (1 := x_le_y).
  Qed.

  Definition new_spec_gt : forall x y : nat, x > y -> IsNone (new x y).
  Proof.
    intros x y x_gt_y.
    unfold new; simpl in *.
    generalize (@leb_complete x y).
    now rewrite leb_correct_conv with (1 := x_gt_y).
  Qed.

  Definition spec (self : t) : left_endpoint self <= right_endpoint self.
  Proof.
    now destruct self as [x y].
  Qed.

  Definition replace_left_endpoint (self : t) (x : nat) : t * option nat :=
    match (x <=? left_endpoint self) as b return (x <=? left_endpoint self = b -> t * option nat) with
    | true => fun x_le_left => (intro (Nat.le_trans (leb_complete x_le_left) (spec self)), Some (left_endpoint self))
    | false => fun _ => (self, None)
    end eq_refl.

  Definition replace_left_endpoint_spec_le : forall (self : t) (x : nat), x <= left_endpoint self -> let (self_new, left_old) := (replace_left_endpoint self x) in Is x (right_endpoint self) self_new /\ IsSome (fun x => left_endpoint self = x) left_old.
  Proof.
    intros [self_x self_y x_le_y] x x_le_self_x.
    unfold replace_left_endpoint; simpl in *.
    generalize (@leb_complete x self_x).
    now rewrite leb_correct with (1 := x_le_self_x).
  Qed.

  Definition replace_left_endpoint_spec_gt : forall (self : t) (x : nat), x > left_endpoint self -> let (self_new, left_old) := (replace_left_endpoint self x) in self_new = self /\ IsNone left_old.
  Proof.
    intros [self_x self_y x_le_y] x x_gt_self_x.
    unfold replace_left_endpoint; simpl in *.
    generalize (@leb_complete x self_x).
    now rewrite leb_correct_conv with (1 := x_gt_self_x).
  Qed.

  Definition replace_right_endpoint (self : t) (y : nat) : t * option nat :=
    match (right_endpoint self <=? y) as b return (right_endpoint self <=? y = b -> t * option nat) with
    | true => fun right_le_y => (intro (Nat.le_trans (spec self) (leb_complete right_le_y)), Some (right_endpoint self))
    | false => fun _ => (self, None)
    end eq_refl.


  Definition replace_right_endpoint_spec_ge : forall (self : t) (y : nat), y >= right_endpoint self -> let (self_new, right_old) := (replace_right_endpoint self y) in Is (left_endpoint self) y self_new /\ IsSome (fun y => right_endpoint self = y) right_old.
  Proof.
    intros [self_x self_y x_le_y] y y_ge_self_y.
    unfold replace_right_endpoint; simpl in *.
    generalize (@leb_complete self_y y).
    now rewrite leb_correct with (1 := y_ge_self_y).
  Qed.

  Definition replace_right_endpoint_spec_lt : forall (self : t) (y : nat), y < right_endpoint self -> let (self_new, right_old) := (replace_right_endpoint self y) in self_new = self /\ IsNone right_old.
  Proof.
    intros [self_x self_y x_le_y] y y_lt_self_y.
    unfold replace_right_endpoint; simpl in *.
    generalize (@leb_complete self_y y).
    now rewrite leb_correct_conv with (1 := y_lt_self_y).
  Qed.

  Definition In : nat -> t -> Prop :=
    fun n interval => left_endpoint interval <= n <= right_endpoint interval.

  Definition not_In : forall (n : nat) (interval : t), ~ In n interval <-> left_endpoint interval > n \/ n > right_endpoint interval.
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
  Defined.

  Definition contains (self : t) (n : nat) : bool :=
    ((left_endpoint self <=? n) && (n <=? right_endpoint self)).

  Definition contains_spec : forall (self : t) (n : nat), In n self <-> contains self n = true.
  Proof.
    intros self n.
    unfold In, contains.
    now rewrite Bool.andb_true_iff, ?Nat.leb_le.
  Defined.

  Definition intersection (self other : t) : option t.
  Proof.
    refine ((if (negb (ltb self other) && negb (ltb other self))%bool as b return ((negb (ltb self other) && negb (ltb other self))%bool = b -> option t) then (fun H => Some (@intro (max (left_endpoint self) (left_endpoint other)) (min (right_endpoint self) (right_endpoint other)) _)) else (fun _ => None)) eq_refl).
    destruct self as [self_l self_r self_le], other as [other_l other_r other_le].
    unfold ltb in H; simpl in *.
    apply andb_true_iff in H as [H₁ H₂]; rewrite <- Nat.leb_antisym, Nat.leb_le in H₁, H₂.
    apply Nat.max_lub; now apply Nat.min_glb.
  Defined.

  Definition intersection_spec_In : forall (self other : t) (n : nat), In n self -> In n other -> IsSome (In n) (intersection self other).
  Proof.
    intros self other n [self₁ self₂] [other₁ other₂].
    assert (H₁ : max (left_endpoint self) (left_endpoint other) <= n) by now apply Nat.max_lub.
    assert (H₂ : n <= min (right_endpoint self) (right_endpoint other)) by now apply Nat.min_glb.
    assert ((negb (ltb self other) && negb (ltb other self))%bool = true).
      unfold ltb.
      rewrite <- ?Nat.leb_antisym, Bool.andb_true_iff, ?Nat.leb_le.
      split; now transitivity n.
    unfold intersection.
    simpl in *.
    destruct self as [self_l self_r self_le], other as [other_l other_r other_le]; unfold ltb in *; simpl in *.
    generalize (andb_true_iff (negb (self_r <? other_l)) (negb (other_r <? self_l))).
    rewrite H.
    intros ?.
    unfold In; simpl.
    now split.
  Defined.

  Definition intersection_spec_not_In : forall self other : t, (forall n : nat, ~ In n self \/ ~ In n other) -> IsNone (intersection self other).
  Proof.
    intros [self_l self_r self_le] [other_l other_r other_le] H.
    unfold intersection, ltb; simpl.
    simpl.
    assert ((negb (self_r <? other_l) && negb (other_r <? self_l))%bool = false).
      unfold ltb.
      rewrite andb_false_iff, <- ?Nat.leb_antisym, ?Nat.leb_gt.
      destruct (le_lt_dec other_l self_r) as [H₁| H₁].
        destruct (le_lt_dec self_l other_r) as [H₂| H₂].
          Ltac reduce_and_try_to_solve := easy.
          destruct (H (max self_l other_l)) as [H'| H']; contradict H'; unfold In; simpl.
            split.
              apply Nat.le_max_l.
            now apply Nat.max_lub.
          split.
            apply Nat.le_max_r.
          now apply Nat.max_lub.
        now right.
      now left.
    unfold intersection.
    simpl.
    generalize (Bool.andb_true_iff (negb (self_r <? other_l)) (negb (other_r <? self_l))).
    now rewrite H0.
  Defined.
End Interval'.

Module Test.
Require Import Coq.FSets.FMaps.

Module Positions (Key : OrderedTypeOrig) (M : Sfun Key).

  Definition is_some (A : Type) (self : option A) : bool :=
    if self then true else false.

  Definition and (A : Type) (self other : option A) : option A :=
    match self with
    | Some _ => other
    | None => None
    end.

  Definition and_then (A B : Type) (self : option A) (f : A -> option B) : option B :=
    match self with
    | Some x => f x
    | None => None
    end.

  Section test.
    Variable A : Type.
    Variable f : A -> option Key.t.
 
    Definition update (key_to_interval : M.t Interval'.t) (key : Key.t) (index : nat) : option (M.t Interval'.t) :=
      let interval :=
        match M.find key key_to_interval with
        | Some interval =>
          let (interval, old_endpoint) := Interval'.replace_right_endpoint interval index in if is_some old_endpoint then Some interval else None
        | None => Interval'.new index index
        end in 
      option_map (fun interval => M.add key interval key_to_interval) interval.

    Function generate (cards : list A) (index : nat) (key_to_interval : M.t Interval'.t) : option (M.t Interval'.t) :=
       match cards with
      | [] => Some key_to_interval
      | head :: tail =>
        match f head with
        | Some key => and_then (update key_to_interval key index) (generate tail (S index))
        | None => generate tail (S index) key_to_interval
        end
      end.

  End test.
End Positions.
End Test.

Module test (Key : OrderedType) (Owner: DecidableType).


Module Import Card := Card Key Owner.
Module Import OrderedFacts := OrderedTypeFacts Key.

Module Talon.
  Import Coq.FSets.FMapInterface Coq.FSets.FMapFacts.

  Module Key' <: DecidableTypeOrig <: OrderedTypeOrig := Backport_OT Key.

  Module Positions (M: Sfun Key').
    Module Import MapFacts := WFacts_fun Key' M.

Definition unwrap_or (A : Type) (self: option A) (default : A) : A :=
  match self with
  | Some x => x
  | None => default
  end.

Module Interval.
  Inductive t : Set :=
  | new : nat -> nat -> t.

  Definition singleton : nat -> t :=
    fun n => new n n.

  Definition lengthen : t -> nat -> t :=
    fun interval right' =>
      match interval with
      | new l r => new l right'
      end.

  Definition left_endpoint : t -> nat :=
    fun self => 
      match self with
      | new left_endpoint right_endpoint => left_endpoint
      end.

  Definition right_endpoint : t -> nat :=
    fun self => 
      match self with
      | new left_endpoint right_endpoint => right_endpoint
      end.
End Interval.

Function update (key_to_interval : M.t Interval.t) (key : Key.t) (index : nat) : M.t Interval.t :=
  M.add key
  (match M.find key key_to_interval with
  | Some interval => Interval.lengthen interval index
  | None => Interval.singleton index
  end) key_to_interval.

Function generate (cards : list Card.t) (index : nat) (key_to_interval : M.t Interval.t) : M.t Interval.t :=
  match cards with
  | [] => key_to_interval
  | Talon head :: tail => generate tail (S index) (update key_to_interval head index)
  | Assigned head :: tail => generate tail (S index) key_to_interval
  end.

  Definition generate_nil : forall (index : nat) (key_to_interval : M.t Interval.t), generate [] index key_to_interval = key_to_interval.
  Proof.
    reflexivity.
  Defined.

  Definition generate_cons_talon_MapsTo : forall (head : Key.t) (tail : list Card.t) (index : nat) (key_to_interval : M.t Interval.t) (interval : Interval.t), M.MapsTo head interval key_to_interval -> generate (Talon head :: tail) index key_to_interval = generate tail (S index) (M.add head (Interval.lengthen interval index) key_to_interval).
  Proof.
    intros head tail index key_to_interval interval head_MapsTo_interval.
    simpl.
    unfold update.
    now rewrite M.find_1 with (1 := head_MapsTo_interval).
  Defined.

  Definition generate_cons_talon_not_In : forall (head : Key.t) (tail : list Card.t) (index : nat) (key_to_interval : M.t Interval.t), ~ M.In head key_to_interval -> generate (Talon head :: tail) index key_to_interval = generate tail (S index) (M.add head (Interval.singleton index) key_to_interval).
  Proof.
    intros head tail index key_to_interval not_In_head.
    simpl.
    unfold update.
    replace (M.find head key_to_interval) with (@None Interval.t) by (symmetry; now apply not_find_in_iff).
    reflexivity.
  Defined.

  Definition generate_cons_assigned : forall (head : Owner.t) (tail : list Card.t) (index : nat) (key_to_interval : M.t Interval.t), generate (Assigned head :: tail) index key_to_interval = generate tail (S index) key_to_interval.
  Proof.
    reflexivity.
  Defined.

  Definition MapsTo_dec : forall [elt : Type] (m : M.t elt) (x : M.key), {value : elt | M.MapsTo x value m} + ~ M.In x m.
  Proof.
    intros elt m x.
    destruct (M.find x m) as [value|] eqn: test; [left| right].
      exists value.
      now apply M.find_2.
    now apply not_find_in_iff.
  Defined.


Definition generate_ind' : forall (P : list Card.t -> nat -> M.t Interval.t -> M.t Interval.t -> Type), (forall (index : nat) (key_to_interval : M.t Interval.t), P [] index key_to_interval key_to_interval) -> (forall (head : Key.t) (tail : list Card.t) (index : nat) (key_to_interval : M.t Interval.t) (interval : Interval.t), M.MapsTo head interval key_to_interval -> P tail (S index) (M.add head (Interval.lengthen interval index) key_to_interval) (generate tail (S index) (M.add head (Interval.lengthen interval index) key_to_interval)) -> P  (Talon head :: tail) index key_to_interval (generate tail (S index) (M.add head (Interval.lengthen interval index) key_to_interval))) -> (forall (head : Key.t) (tail : list Card.t) (index : nat) (key_to_interval : M.t Interval.t), ~ M.In head key_to_interval -> P tail (S index) (M.add head (Interval.singleton index) key_to_interval) (generate tail (S index) (M.add head (Interval.singleton index) key_to_interval)) -> P (Talon head :: tail) index key_to_interval (generate tail (S index) (M.add head (Interval.singleton index) key_to_interval))) -> (forall (head : Owner.t) (tail : list Card.t) (index : nat) (key_to_interval : M.t Interval.t), P tail (S index) key_to_interval (generate tail (S index) key_to_interval) -> P (Assigned head :: tail) index key_to_interval (generate tail (S index) key_to_interval)) -> forall (cards : list Card.t) (index : nat) (key_to_interval : M.t Interval.t), P cards index key_to_interval (generate cards index key_to_interval).
Proof.
  intros P P_nil P_cons_talon_MapsTo P_cons_talon_not_In P_assigned .
  simpl in *.
  intros cards.
  induction cards as [| [head| head] tail IHtail]; intros index key_to_interval.
      apply P_nil.
    specialize (IHtail (S index) (update key_to_interval head index)).
    destruct (MapsTo_dec key_to_interval head) as [(interval & head_MapsTo_interval)| not_In_head].
      rewrite generate_cons_talon_MapsTo with (1 := head_MapsTo_interval).
      assert (update key_to_interval head index = M.add head (Interval.lengthen interval index) key_to_interval) as e.
        unfold update.
        now rewrite M.find_1 with (1 := head_MapsTo_interval).
      rewrite e in IHtail.
      now apply P_cons_talon_MapsTo.
    rewrite generate_cons_talon_not_In with (1 := not_In_head).
    assert (update key_to_interval head index = M.add head (Interval.singleton index) key_to_interval) as e.
      unfold update.
      replace (M.find head key_to_interval) with (@None Interval.t).
        reflexivity.
      symmetry; now apply not_find_in_iff.
    rewrite e in IHtail.
    simpl in *.
    now apply P_cons_talon_not_In.
  apply P_assigned.
  specialize (IHtail (S index) key_to_interval).
  apply IHtail.
Defined.

Definition generate_complete : forall (key : Key.t) (cards : list (Card.t)) (index : nat) (key_to_interval : M.t Interval.t), M.In key key_to_interval \/ InA Card.eq (Talon key) cards <-> M.In key (generate cards index key_to_interval).
Proof.
  intros key cards index key_to_interval.
  functional induction (generate cards index key_to_interval) as [| ? index key_to_interval head tail ? IHtail| ? index key_to_interval head tail ? IHtail].
      rewrite InA_nil.
      firstorder.
    rewrite InA_cons, <- IHtail.
    cut (M.In key key_to_interval \/ eq (Talon key) (Talon head) <->
M.In key (update key_to_interval head index)).
      firstorder.
    unfold update.
    rewrite add_in_iff.
    simpl.
    assert (Key.eq key head <-> Key.eq head key) as -> by easy.
    firstorder.
  rewrite <- IHtail.
  assert (InA eq (Talon key) (Assigned head :: tail) <-> InA eq (Talon key) tail) as ->.
    rewrite InA_cons.
    simpl.
    firstorder.
  firstorder.
Defined.
(*
Definition generate_complete : forall (key : Key.t) (cards : list (Card.t)) (index : nat) (key_to_interval : M.t Interval.t), M.In key key_to_interval \/ InA Card.eq (Talon key) cards -> M.In key (generate cards index key_to_interval).
Proof.
  intros key cards index key_to_interval.
  functional induction (generate cards index key_to_interval) as [| ? index key_to_interval head tail ? IHtail| ? index key_to_interval head tail ? IHtail]; intros In_key.
      destruct In_key  as [In_key| In_key]; [assumption|].
      now rewrite InA_nil in In_key.
    destruct In_key as [In_key| In_key]; apply IHtail; [left|].
      now apply add_in_iff; right.
    apply InA_cons in In_key as [key_eq_head| In_key]; [left| right].
      unfold update.
      now apply add_in_iff; left.
    assumption.
  destruct In_key as [In_key| In_key]; apply IHtail; [left| right].
    assumption.
  apply InA_cons in In_key as [key_eq_head| In_key].
    contradiction.
  assumption.
Defined.
*)
Module Option := Option Card.

Definition generate_left_const : forall (key : Key.t) (cards : list (Card.t)) (index : nat) (key_to_interval : M.t Interval.t) (interval : Interval.t), M.MapsTo key interval key_to_interval -> exists right_endpoint : nat, M.MapsTo key (Interval.new (Interval.left_endpoint interval) right_endpoint) (generate cards index key_to_interval).
Proof.
  intros key cards index key_to_interval.
  functional induction (generate cards index key_to_interval) as [| ? index key_to_interval head tail ? IHtail| ? index key_to_interval head tail ? IHtail]; intros interval MapsTo_key_interval.
      destruct interval as [left_endpoint right_endpoint].
      now exists right_endpoint.
    destruct (Key.eq_dec head key) as [head_eq_key| head_neq_key].
      assert (M.MapsTo key (Interval.lengthen interval index) (update key_to_interval head index)) as H.
        unfold update.
        rewrite M.find_1 with (e := interval).
          now apply M.add_1.
        now rewrite head_eq_key.
      destruct IHtail with (1 := H) as [right_endpoint H'].
      destruct interval as [left_endpoint' right_endpoint'].
      simpl in *.
      exists right_endpoint.
      assumption.
    now apply IHtail, M.add_2.
  now apply IHtail.
Defined.

Definition generate_right_const : forall (key : Key.t) (cards : list (Card.t)) (index : nat) (key_to_interval : M.t Interval.t), ~ InA Card.eq (Talon key) cards -> option_map Interval.right_endpoint (M.find key key_to_interval) = option_map Interval.right_endpoint (M.find key (generate cards index key_to_interval)).
Proof.
  intros key cards index key_to_interval.
  functional induction (generate cards index key_to_interval) as [| ? index key_to_interval head tail ? IHtail| ? index key_to_interval head tail ? IHtail]; intros not_In_key.
      reflexivity.
    assert (~ Key.eq key head /\ ~ InA Card.eq (Talon key) tail) as [key_neq_head not_In_key_tail].
      cut (~ (Key.eq key head \/ InA eq (Talon key) tail)).
        auto.
      contradict not_In_key.
      now apply InA_cons.
    rewrite <- IHtail with (1 := not_In_key_tail).
    unfold update.
    now rewrite add_neq_o; [| contradict key_neq_head].
  apply IHtail.
  contradict not_In_key.
  now constructor 2.
Defined.


Definition generate_left_new : forall (key : Key.t) (cards : list (Card.t)) (index : nat) (key_to_interval : M.t Interval.t), ~ M.In key key_to_interval -> forall interval : Interval.t, M.MapsTo key interval (generate cards index key_to_interval) -> exists offset : nat, Interval.left_endpoint interval = index + offset /\ (forall n : nat, n < offset -> ~ Option.eq (nth_error cards n) (Some (Talon key))) /\ Option.eq (nth_error cards offset) (Some (Talon key)).
Proof.
  intros key cards index key_to_interval.
  functional induction (generate cards index key_to_interval) as [| ? index key_to_interval head tail ? IHtail| ? index key_to_interval head tail ? IHtail]; intros not_In_key interval MapsTo_key_interval.
      contradict not_In_key.
      now exists interval.
    destruct (Key.eq_dec head key) as [head_eq_key| head_neq_key].
      exists 0.
      repeat split.
          rewrite PeanoNat.Nat.add_0_r.
          assert (M.MapsTo key (Interval.singleton index) (update key_to_interval head index)).
            unfold update.
            rewrite head_eq_key.
            replace (M.find key key_to_interval) with (@None Interval.t).
              now apply M.add_1.
            symmetry.
            now apply not_find_in_iff.
          destruct (@generate_left_const key tail (S index) _ _ H) as [right_endpoint H'].
          replace interval with (Interval.new index right_endpoint).
            reflexivity.
          now apply MapsTo_fun with (1 := H').
        intros n n_lt_0.
        contradict n_lt_0.
        apply PeanoNat.Nat.nlt_0_r.
      assumption.
    assert (~ M.In key (update key_to_interval head index)) as H.
      unfold update.
      now rewrite add_neq_in_iff.
    specialize (IHtail H interval MapsTo_key_interval).
    destruct IHtail as [offset (H₁ & H₂ & H₃)].
    exists (S offset).
    repeat split.
        now rewrite PeanoNat.Nat.add_succ_r.
      destruct n as [| n].
        easy.
      intros n_lt_offset.
      now apply H₂, Lt.lt_S_n.
    assumption.
  specialize (IHtail not_In_key interval MapsTo_key_interval).
  destruct IHtail as [offset (H₁ & H₂ & H₃)].
  exists (S offset).
  repeat split.
      now rewrite PeanoNat.Nat.add_succ_r.
    destruct n as [| n].
      easy.
    intros n_lt_offset.
    now apply H₂, Lt.lt_S_n.
  assumption.
Defined.

Functional Scheme nth_error_ind := Induction for nth_error Sort Prop.

Definition nth_error_InA : forall (key : Key.t) (index : nat) (cards : list Card.t), Option.eq (nth_error cards index) (Some (Talon key)) -> InA Card.eq (Talon key) cards.
Proof.
  intros key index.
  induction index as [| index' IHindex']; intros [| head tail] H; try contradiction.
    now constructor 1.
  now constructor 2; apply IHindex'.
Defined.

Definition generate_right_new : forall (key : Key.t) (cards : list (Card.t)) (index : nat) (key_to_interval : M.t Interval.t), InA Card.eq (Talon key) cards -> forall interval : Interval.t, M.MapsTo key interval (generate cards index key_to_interval) -> exists offset : nat, Interval.right_endpoint interval = index + offset /\ (forall n : nat, n > offset -> ~ Option.eq (nth_error cards n) (Some (Talon key))) /\ Option.eq (nth_error cards offset) (Some (Talon key)).
Proof.
  intros key cards index key_to_interval.
  functional induction (generate cards index key_to_interval) as [| ? index key_to_interval head tail ? IHtail| ? index key_to_interval head tail ? IHtail]; intros In_key_cards interval MapsTo_key_interval.
      now apply InA_nil in In_key_cards.
    destruct (InA_dec Card.eq_dec (Talon key) tail) as [In_key_tail| not_In_key_tail].
      destruct IHtail with (1 := In_key_tail) (2 := MapsTo_key_interval) as [offset (H₁ & H₂ & H₃)].
      exists (S offset).
      repeat split.
          now rewrite PeanoNat.Nat.add_succ_r.
        destruct n as [| n].
          easy.
        intros n_lt_offset.
        now apply H₂, Lt.lt_S_n.
      assumption.
    assert (Key.eq key head) as key_eq_head by now apply InA_cons in In_key_cards as [key_eq_head| In_key_tail].
    exists 0.
    repeat split.
        rewrite PeanoNat.Nat.add_0_r.
        pose (H := generate_right_const (S index) (update key_to_interval head index) not_In_key_tail).
        cut (Some (Interval.right_endpoint interval) = Some index).
          now inversion 1.
        transitivity (option_map Interval.right_endpoint (M.find key (generate tail (S index) (update key_to_interval head index)))).
          now rewrite M.find_1 with (1 := MapsTo_key_interval).
        transitivity (option_map Interval.right_endpoint (M.find key (update key_to_interval head index))).
          easy.
        unfold update.
        rewrite add_eq_o by easy.
        now destruct (M.find head key_to_interval) as [[left_endpoint right_endpoint]|].
      intros [| n'] n_gt_0.
        contradict n_gt_0.
        apply PeanoNat.Nat.lt_irrefl.
      simpl.
      contradict not_In_key_tail.
      now apply nth_error_InA with n'.
    easy.
  assert (InA Card.eq (Talon key) tail) as In_key_tail by now apply InA_cons in In_key_cards as [key_eq_head| In_key_tail].
  destruct IHtail with (1 := In_key_tail) (2 := MapsTo_key_interval) as [offset (H₁ & H₂ & H₃)].
  exists (S offset).
  repeat split.
      now rewrite PeanoNat.Nat.add_succ_r.
    destruct n as [| n].
      easy.
    intros n_lt_offset.
    now apply H₂, Lt.lt_S_n.
  assumption.
Defined.


(*
Definition generate_lol : forall (cards : list (Card.t)) (index : nat) (key_to_interval : M.t Interval.t) (key : Key.t), ~ M.In key key_to_interval -> forall interval : Interval.t, M.MapsTo key interval (generate cards index key_to_interval) -> exists n : nat, Interval.left_endpoint interval = n + index /\ Option.eq (nth_error cards n) (Some (Talon key)).
Proof.
  intros cards.
  induction cards as [| [head| head] tail IHtail]; intros index key_to_interval key not_In_key_intervals interval MapsTo_key_interval.
      assert (M.In key key_to_interval) by now exists interval.
      contradiction.
    specialize (IHtail (S index) (update key_to_interval head index) key).
    destruct (Key.eq_dec head key) as [head_eq_key| head_neq_key].
      simpl in *.
      unfold update in *.
      simpl in *.
      replace (M.find head key_to_interval) with (@None Interval.t) in MapsTo_key_interval.
        assert (M.MapsTo key (Interval.singleton index) (M.add head (Interval.singleton index) key_to_interval)) as H.
          now apply M.add_1.
        destruct (@generate_left_endpoint tail (S index) (M.add head (Interval.singleton index) key_to_interval) key (Interval.singleton index) H) as [right_endpoint H'].
        Search (M.MapsTo _ _ _ -> _ = _).
        simpl in *.
        assert (interval = Interval.new index right_endpoint) as ->.
          now apply MapsTo_fun with (1 := MapsTo_key_interval).
        simpl.
        exists 0.
        split.
          reflexivity.
        assumption.
      symmetry.
      apply not_find_in_iff.
      now rewrite head_eq_key.
    assert (~ M.In key (update key_to_interval head index)) as not_In_key_update.
      intros In_key_update.
      apply add_neq_in_iff in In_key_update.
        contradiction.
      assumption.
    specialize (IHtail not_In_key_update interval MapsTo_key_interval).
    destruct IHtail as [n [H₁ H₂]].
    exists (S n).
    split.
      now rewrite PeanoNat.Nat.add_succ_r in H₁.
    assumption.
  specialize (IHtail (S index) key_to_interval key not_In_key_intervals interval MapsTo_key_interval).
  destruct IHtail as [n [H₁ H₂]].
  exists (S n).
  split.
    now rewrite PeanoNat.Nat.add_succ_r in H₁.
  assumption.
Defined.
*)
(*
Definition generate_not_in : forall (cards : list (Card.t)) (index : nat) (key_to_interval : M.t Interval.t) (key : Key.t), ~ Exists (card_eq (Talon _ key)) cards -> forall interval : Interval.t, M.MapsTo key interval (generate cards index key_to_interval) <-> M.MapsTo key interval key_to_interval.
Proof.
  intros cards.
  induction cards as [| head tail IHtail]; intros index key_to_interval key not_In_key_cards interval.
    reflexivity.
  assert (~ Exists (card_eq (Talon Owner.t key)) tail) as not_In_key_tail.
    contradict not_In_key_cards.
    now constructor 2.
  assert (~ card_eq (Talon Owner.t key) head) as key_neq_head.
    contradict not_In_key_cards.
    now constructor 1.
  destruct head as [head| head].
    simpl in *.
    specialize (IHtail (S index) (update key_to_interval head index) key not_In_key_tail interval).
    assert (M.MapsTo key interval (update key_to_interval head index) <-> M.MapsTo key interval key_to_interval) as H.
      unfold update.
      rewrite add_neq_mapsto_iff.
        reflexivity.
      now contradict key_neq_head.
    now rewrite H in IHtail.
  now apply IHtail.
Defined.

Definition generate_lol_final : forall (cards : list (Card.t)) (index : nat) (key_to_interval : M.t Interval.t) (key : Key.t), Exists (card_eq (Talon _ key)) cards -> forall interval : Interval.t, M.MapsTo key interval (generate cards index key_to_interval) -> exists n : nat, Interval.right_endpoint interval = n + index /\ option_eq card_eq (nth_error cards n) (Some (Talon _ key)).
Proof.
  intros cards.
  induction cards as [| [head| head] tail IHtail]; intros index key_to_interval key In_key_cards interval MapsTo.
      now rewrite Exists_nil in In_key_cards.
    specialize (IHtail (S index) (update key_to_interval head index) key).
    destruct (Exists_dec _ tail (@card_eq_dec (Talon _ key))) as [In_key_tail| not_In_key_tail].
      specialize (IHtail In_key_tail _ MapsTo).
      destruct IHtail as [n [H₁ H₂]].
      exists (S n).
      split.
        now rewrite PeanoNat.Nat.add_succ_r in H₁.
      assumption.
    apply Exists_cons in In_key_cards as [key_eq_head| In_key_tail].
      simpl in key_eq_head.
      simpl in MapsTo.
      rewrite generate_not_in in MapsTo by assumption.
      unfold update in *.
      Search (M.MapsTo _ _ (M.add _ _ _)).
      rewrite add_mapsto_iff in MapsTo.
      destruct MapsTo as [[_ e]| [? ?]].
        rewrite <- e.
        replace (  Interval.right_endpoint
    match M.find head key_to_interval with
    | Some interval0 => Interval.lengthen interval0 index
    | None => Interval.singleton index
    end) with index.
          exists 0.
          split.
            reflexivity.
          simpl.
          now symmetry.
        now destruct (M.find head key_to_interval) as [[? ?]|]; simpl.
      now contradict H.
    contradiction.
  apply Exists_cons in In_key_cards as [key_eq_head| In_key_tail].
    contradiction.
  specialize (IHtail (S index) key_to_interval key In_key_tail interval MapsTo).
  destruct IHtail as (n & [H₁ H₂]).
  exists (S n).
  split.
    now rewrite PeanoNat.Nat.add_succ_r in H₁.
  assumption.
Defined.
*)
Definition intervals : list (Card.t) -> M.t Interval.t :=
  fun cards => generate cards 0 (M.empty _).

Definition intervals_complete : forall (cards : list (Card.t)) (key : Key.t), InA Card.eq (Talon key) cards -> M.In key (intervals cards).
Proof.
  intros cards key In_key_cards.
  apply generate_complete.
  now right.
Defined.

Definition intervals_correct : forall (cards : list Card.t) (key : Key.t) (interval : Interval.t), M.MapsTo key interval (intervals cards) -> (forall n : nat, n < (Interval.left_endpoint interval) -> ~ Option.eq (nth_error cards n) (Some (Talon key))) /\ Option.eq (nth_error cards (Interval.left_endpoint interval)) (Some (Talon key)) /\  Option.eq (nth_error cards (Interval.right_endpoint interval)) (Some (Talon key)) /\ (forall n : nat, n > (Interval.right_endpoint interval) -> ~ Option.eq (nth_error cards n) (Some (Talon key))).
Proof.
  intros cards key interval MapsTo_key_interval.
  assert (M.In key (intervals cards)) as In_key by now exists interval.
  assert (InA Card.eq (Talon key) cards) as In_key_cards.
    apply generate_complete in In_key.
    rewrite empty_in_iff in In_key.
    firstorder.
  assert (~ M.In key (M.empty Interval.t)) as not_In_key by now rewrite empty_in_iff.
  destruct generate_left_new with (1 := not_In_key) (2 := MapsTo_key_interval) as [left_endpoint (left_H₁ & left_H₂ & left_H₃)].
  destruct generate_right_new with (1 := In_key_cards) (2 := MapsTo_key_interval) as [right_endpoint (right_H₁ & right_H₂ & right_H₃)].
  rewrite right_H₁, left_H₁.
  simpl.
  repeat split; try assumption.
Defined.
(*
Definition intervals_correct_iff : forall (cards : list Card.t) (key : Key.t) (interval : Interval.t), M.MapsTo key interval (intervals cards) <-> (forall n : nat, n < (Interval.left_endpoint interval) -> ~ Option.eq (nth_error cards n) (Some (Talon key))) /\ Option.eq (nth_error cards (Interval.left_endpoint interval)) (Some (Talon key)) /\  Option.eq (nth_error cards (Interval.right_endpoint interval)) (Some (Talon key)) /\ (forall n : nat, n > (Interval.right_endpoint interval) -> ~ Option.eq (nth_error cards n) (Some (Talon key))).
Proof.
  intros cards key interval.
  split.
    apply intervals_correct.
  destruct 1 as (H₂_left & H₃_left & H₂_right & H₃_right).
Admitted.*)
End Positions.

Import Coq.MSets.MSetFacts Coq.MSets.MSetProperties.

Module Owners (M : WSetsOn Owner).

Module Import Facts := WFactsOn Owner M.
Module Import Properties := WPropertiesOn Owner M.

Definition owners_helper : list (Card.t) -> M.t -> list Owner.t.
Proof.
  intros cards.
  induction cards as [| [key| owner] tail IHtail]; intros seen.
    exact [].
  exact (IHtail seen).
  exact (if M.mem owner seen then IHtail seen else owner:: IHtail (M.add owner seen)).
Defined.

Definition owners: list (Card.t) ->list Owner.t :=
fun cards => owners_helper cards M.empty.

Definition owners_subset : forall (cards: list (Card.t)) (seen seen' : M.t), M.Subset seen seen' -> forall owner, Exists (Owner.eq owner) (owners_helper cards seen') -> Exists (Owner.eq owner) (owners_helper cards seen).
Proof.
  intros cards.
  induction cards as [| [head_key| head_owner] tail IHtail]; intros seen seen' seen_le_seen' owner.
      easy.
    now apply IHtail.
  simpl.
  destruct (M.mem head_owner seen) eqn: mem_head_seen.
    assert (M.mem head_owner seen' = true) as ->.
      rewrite M.mem_spec.
      apply seen_le_seen'.
      now rewrite <- M.mem_spec.
    now apply IHtail.
  destruct (M.mem head_owner seen') eqn: mem_head_seen'.  
    intros In_owner_seen'.
    right.
    apply IHtail with seen'.
      apply subset_add_3.
        now apply M.mem_spec.
      assumption.
    assumption.
  simpl.
  intros H.
  apply Exists_cons in H.
  destruct H.
    now left.
  right.
  apply IHtail with (M.add head_owner seen').
    simpl.
    now apply add_s_m.
  assumption.
Defined.

Definition helper_complete : forall (cards: list (Card.t)) (seen: M.t) (owner : Owner.t), ~ M.In owner seen -> Exists (Owner.eq owner) (owners_helper cards seen) <-> Exists (Card.eq (Assigned owner)) cards.
Proof.
  induction cards as [| [head_key| head_owner] tail IHtail]; intros seen owner In_owner_seen.
      now rewrite ?Exists_nil.
    simpl.
    assert (Exists (Card.eq (Assigned owner)) (Talon head_key :: tail) <-> Exists (Card.eq (Assigned owner)) tail) as ->.
      split.
        intros H.
        apply Exists_cons in H.
        destruct H as [owner_eq_head| In_owner_tail].
          contradiction.
        assumption.
      intros In_owner_tail.
      now right.
    now apply IHtail.
  simpl.
  split.
    destruct (M.mem head_owner seen) eqn: mem_head_owner_seen.
      intro In_owner_tail.
      right.
      now apply IHtail with seen.
    simpl.
    intros H.
    apply Exists_cons in H.
    destruct H as [e| In_owner_tail].
      now left.
    destruct (Owner.eq_dec owner head_owner).
      now left.
    right.
    apply IHtail with (seen := seen).
      assumption.
    apply owners_subset with (seen' := (M.add head_owner seen)).
      now apply subset_add_2.
    assumption.
  intros H.
  apply Exists_cons in H.
  destruct H as [head_owner_eq_owner| In_owner_tail].
    simpl in head_owner_eq_owner.
    rewrite <- head_owner_eq_owner.
    destruct (M.mem owner seen) eqn: mem_owner_seen.
      now rewrite M.mem_spec in mem_owner_seen.
    now left.
  simpl.
  destruct (M.mem head_owner seen) eqn: mem_head_owner_seen.
    now apply IHtail.
  (*specialize (IHtail seen owner In_owner_seen).*)
  destruct (Owner.eq_dec owner head_owner) as [owner_eq_head_owner| owner_neq_head_owner].
    left.
    assumption.
  right.
  assert (Exists (Owner.eq owner) (owners_helper tail seen)).
    now rewrite IHtail.
  rewrite (IHtail (M.add head_owner seen) owner).
    assumption.
  intros H'.
  rewrite M.add_spec in H'.
  destruct H' as [owner_eq_head_owner| In_owner_seen'].
    contradiction.
  contradiction.
Defined.

End Owners.




Definition owners : list (Card.t) -> list Owner.t.
Proof.
  intros cards.
  induction cards as [| head tail IHtail].
    exact [].
  destruct head as [key| owner].
    exact IHtail.
  exact (owner :: IHtail).
Defined.

End Talon.
End test.

Module Test2.
Import Coq.FSets.FMaps.
Import Coq.FSets.FMapFacts.

Definition unwrap_or (A : Type) (self: option A) (default : A) : A :=
  match self with
  | Some x => x
  | None => default
  end.

  Definition and_then (A B : Type) (self : option A) (f : A -> option B) : option B :=
    match self with
    | Some x => f x
    | None => None
    end.

  Definition IsSome : forall A : Type, (A -> Prop) -> option A -> Prop :=
    fun A P x =>
      match x with
      | Some x' => P x'
      | _ => False
      end.

  Definition IsNone : forall A : Type, option A -> Prop :=
    fun A x =>
      match x with
      | Some _ => False
      | _ => True
      end.

  Definition Is : forall A : Type, (A -> Prop) -> Prop -> option A -> Prop :=
    fun A P Q x =>
      match x with
      | Some x' => P x'
      | None => Q
      end.

Module Coloring (Owner : DecidableType) (M : WSfun Owner).
      Module Import MapFacts := WFacts_fun Owner M.

  Inductive Opcode : Set :=
  | Up : Opcode
  | Down : Opcode.
(*  | Both : Opcode.*)

  Definition Correct (colors : nat) (coloring : M.t nat) : Prop :=
    forall color : nat, color < colors <-> (exists owner : Owner.t, M.MapsTo owner color coloring).
(*
  Definition Correct (colors : nat) (coloring : M.t nat) : Prop :=
    (forall (owner : Owner.t) (color : nat), M.MapsTo owner color coloring -> color < colors) /\ (forall color : nat, color < colors -> exists owner : Owner.t, M.MapsTo owner color coloring).
*)
  Lemma Correct_empty : Correct 0 (M.empty _).
  Proof.
    intros color.
    split.
      intros color_lt_colors.
      contradict color_lt_colors.
      apply PeanoNat.Nat.nlt_0_r.
    intros [owner H].
    contradict H.
    apply M.empty_1.
  Qed.

  Lemma Correct_add_new : forall (colors : nat) (coloring : M.t nat), Correct colors coloring -> forall owner : Owner.t, ~ M.In owner coloring -> Correct (S colors) (M.add owner colors coloring).
  Proof.
    intros colors coloring Correct owner not_In.
    split.
      intros lt.
      apply Lt.le_lt_or_eq in lt as [lt| b].
        apply Lt.lt_S_n, Correct in lt as [owner' H'].
        exists owner'.
        Search (M.MapsTo _ _ (M.add _ _ _)).
        apply M.add_2.
          contradict not_In.
          assert (M.In owner' coloring) by now exists color.
          now apply In_iff with owner'.
        assumption.
      apply eq_add_S in b as ->.
      exists owner.
      Search M.MapsTo.
      now apply M.add_1.
    intros [owner' H].
    apply add_mapsto_iff in H as [[eq <-]| [neq H]].
      auto.
    apply PeanoNat.Nat.lt_lt_succ_r, Correct.
    now exists owner'.
  Qed.

  Lemma Correct_add_unused : forall (colors : nat) (coloring : M.t nat), Correct colors coloring -> forall owner : Owner.t, ~ M.In owner coloring -> forall color : nat, color < colors -> Correct colors (M.add owner color coloring).
  Proof.
    intros colors coloring Correct owner not_In color color_lt_colors color'.
    split.
      intros color'_lt_colors.
      apply Correct in color'_lt_colors as [owner' H].
      exists owner'.
      assert (neq : ~ Owner.eq owner owner').
        contradict not_In.
        exists color'.
        now apply MapsTo_iff with owner'.
      now apply M.add_2.
    intros [owner' H].
    apply add_mapsto_iff in H as [(eq & ->)| (neq & H)].
      assumption.
    apply Correct; now exists owner'.
  Qed.

  Fixpoint regular (instructions : list (Opcode * Owner.t)) (colors : nat) (coloring : M.t nat) (unused_colors : list nat) : option (nat * M.t nat) :=
    match instructions with
    | (opcode, owner) :: tail => 
      match opcode with
      | Up =>
        match unused_colors with
        | u₀ :: x₀ => regular tail colors (M.add owner u₀ coloring) x₀
        | [] => regular tail (S colors) (M.add owner colors coloring) []
        end
      | Down => and_then (M.find owner coloring) (fun color => regular tail colors coloring (color :: unused_colors))
      end
    | [] => Some (colors, coloring)
    end.

  Inductive Nth (A : Type) (P : A -> Prop) : list A -> nat -> Prop :=
  | Nth_O : forall (u₀ : A) (x₀ : list A), P u₀ -> Nth P (u₀ :: x₀) O
  | Nth_S : forall (x₀ : list A) (n : nat), Nth P x₀ n -> forall u₀ : A, Nth P (u₀ :: x₀) (S n).

  Definition Correct_instruction : list (Opcode * Owner.t) -> Owner.t -> Prop.
  Proof.
    intros instructions owner.
    refine (exists left right : nat, _).
    exact (forall n : nat, n <> left /\ n <> right -> Nth (fun H => ~ Owner.eq (snd H) owner) instructions n /\ Nth (fun H => fst H = Up /\ Owner.eq (snd H) owner) instructions left /\ Nth (fun H => fst H = Down /\ Owner.eq (snd H) owner) instructions right).
  Defined.

  Definition Instruction_Rel : (Opcode * Owner.t) -> (Opcode * Owner.t) -> Prop :=
    fun self other =>
      let (self_opcode, self_owner) := self in
      let (other_opcode, other_owner) := other in
      ~ Owner.eq self_owner other_owner \/ self_opcode = Up /\ other_opcode = Down.

  Definition InstructionsOk : list (Opcode * Owner.t) -> Prop :=
    ForallOrdPairs Instruction_Rel.

  Definition Forall_iff : forall (A : Type) (P : A -> Prop) (u₀ : A) (x₀ : list A), Forall P (u₀ :: x₀) <-> P u₀ /\ Forall P x₀.
  Proof.
    split; intros H.
      split.
        now apply Forall_inv with x₀.
      now apply Forall_inv_tail with u₀.
    destruct H as [H₁ H₂].
    now constructor.
  Defined.

  Definition Forall_InA : forall (A : Type) (eqA : A -> A -> Prop) (P : A -> Prop), Proper (eqA ==> iff) P -> forall (u : A) (y : list A), InA eqA u y -> Forall P y -> P u.
  Proof.
    intros A eqA P Proper_P u y.
    induction 1 as [v₀ y₀ u_eq_v₀| v₀ y₀ In_y₀ IHy₀]; intros P_y.
      rewrite u_eq_v₀.
      now apply Forall_inv with y₀.
    now apply IHy₀, Forall_inv_tail with v₀.
  Qed.

  Definition instruction_eq : (Opcode * Owner.t) -> (Opcode * Owner.t) -> Prop :=
    fun self other =>
      let (self_opcode, self_owner) := self in
      let (other_opcode, other_owner) := other in
      self_opcode = other_opcode /\ Owner.eq self_owner other_owner.

  Instance Instruction_Rel_Proper : forall instruction : Opcode * Owner.t, Proper (instruction_eq ==> iff) (Instruction_Rel instruction).
  Proof.
    intros [opcode₁ owner₁] [opcode₂ owner₂] [opcode₃ owner₃] [H₁ H₂].
    simpl in *.
    now rewrite H₁, H₂.
  Defined.

  Definition invariant (instructions : list (Opcode * Owner.t)) (colors : nat) (coloring : M.t nat) (unused_colors : list nat) : Prop := Correct colors coloring /\ (forall owner : Owner.t, M.In owner coloring -> ~ InA instruction_eq (Up, owner) instructions) /\ InstructionsOk instructions /\ Forall (fun color => exists owner : Owner.t, M.MapsTo owner color coloring) unused_colors.

  Definition invariant_nil : forall (colors : nat) (coloring : M.t nat) (unused_colors : list nat), invariant [] colors coloring unused_colors -> Correct colors coloring.
  Proof.
    intros colors coloring unused_colors (H₁ & H₂ & H₃).
    assumption.
  Defined.

  Definition InA_cons_iff : forall (A : Type) (eqA : A -> A -> Prop) (u v₀ : A) (y₀ : list A), ~ InA eqA u (v₀ :: y₀) <-> ~ eqA u v₀ /\ ~ InA eqA u y₀.
  Proof.
    intros A eqA u v₀ y₀.
    rewrite InA_cons.
    firstorder.
  Defined.

  Definition FOP_cons_inv : forall (A : Type) (R : A -> A -> Prop) (u₀ : A) (x₀ : list A), ForallOrdPairs R (u₀ :: x₀) <-> Forall (R u₀) x₀ /\ ForallOrdPairs R x₀.
  Proof.
    split.
      now inversion 1.
    now constructor.
  Defined.

  Definition invariant_cons_up_nil : forall (owner : Owner.t) (tail : list (Opcode * Owner.t)) (colors : nat) (coloring : M.t nat), invariant ((Up, owner) :: tail) colors coloring [] -> invariant tail (S colors) (M.add owner colors coloring) [].
  Proof.
    intros owner tail colors coloring (H₁ & H₂ & H₃ & H4).
    split.
      apply Correct_add_new with (1 := H₁).
      intros In_owner_coloring.
      apply H₂, InA_cons_iff in In_owner_coloring as [eq _].
      contradict eq.
      split; reflexivity.
    split.
      intros owner' In_owner'.
      apply add_in_iff in In_owner' as [eq| In_owner'].
        contradict H₃.
        intros X.
        apply FOP_cons_inv in X as [X _].
        assert (Instruction_Rel (Up, owner) (Up, owner')).
          apply Forall_InA with (2 := H₃) (3 := X).
          apply Instruction_Rel_Proper.
        simpl in H.
        destruct H.
          easy.
        discriminate (proj2 H).
      now apply H₂, InA_cons_iff in In_owner'.
    split.
      now inversion H₃.
    constructor.
  Defined.

  Definition invariant_cons_up_cons : forall (owner : Owner.t) (tail : list (Opcode * Owner.t)) (colors : nat) (coloring : M.t nat) (u₀ : nat) (x₀ : list nat), invariant ((Up, owner) :: tail) colors coloring (u₀ :: x₀) -> invariant tail colors (M.add owner u₀ coloring) x₀.
  Proof.
    intros owner tail colors coloring u₀ x₀ (H1 & H2 & H3 & H4).
    split.
      apply Correct_add_unused with (1 := H1).
        intros In_owner_coloring.
        apply H2, InA_cons_iff in In_owner_coloring as [eq _].
        contradict eq.
        split; reflexivity.
      apply H1.
      now apply Forall_inv in H4.
    split.
      intros owner' In_owner'.
      apply add_in_iff in In_owner' as [eq| In_owner'].
        contradict H3.
        intros X.
        apply FOP_cons_inv in X as [X _].
        assert (Instruction_Rel (Up, owner) (Up, owner')).
          apply Forall_InA with (2 := H3) (3 := X).
          apply Instruction_Rel_Proper.
        simpl in H.
        destruct H.
          easy.
        discriminate (proj2 H).
      now apply H2, InA_cons_iff in In_owner'.
    split.
      now apply FOP_cons_inv in H3.
    apply Forall_inv_tail in H4.
    apply Forall_impl with (2 := H4).
    intros color [owner' owner'_to_color].
    exists owner'.
    apply M.add_2.
      apply FOP_cons_inv in H3.
      intros owner_eq_owner'.
      assert (~ InA instruction_eq (Up, owner') ((Up, owner) :: tail)).
        apply H2.
        now exists color.
      apply InA_cons_iff in H as [H _].
      apply H.
      easy.
    assumption.
  Defined.

  Definition invariant_cons_down : forall (owner : Owner.t) (tail : list (Opcode * Owner.t)) (colors : nat) (coloring : M.t nat) (unused_colors : list nat), invariant ((Down, owner) :: tail) colors coloring unused_colors -> forall color : nat, M.MapsTo owner color coloring -> invariant tail colors coloring (color :: unused_colors).
  Proof.
    intros owner tail colors coloring unused_colors (H1 & H2 & H3 & H4) color MapsTo_owner_color.
    split.
      assumption.
    split.
      intros owner' In_owner'.
      now apply H2, InA_cons_iff in In_owner'.
    split.
      now apply FOP_cons_inv in H3.
    constructor.
      now exists owner.
    assumption.
  Defined.
(*
  Definition invariant (instructions : list (Opcode * Owner.t)) (colors : nat) (coloring : M.t nat) (unused_colors : list nat) : Prop := Correct colors coloring /\ (forall owner : Owner.t, M.In owner coloring -> Forall (fun H => fst H = Down \/ ~ Owner.eq (snd H) owner) instructions) /\ Forall (fun color => exists owner : Owner.t, M.MapsTo owner color coloring) unused_colors.

  Definition invariant_nil : forall (colors : nat) (coloring : M.t nat) (unused_colors : list nat), invariant [] colors coloring unused_colors -> Correct colors coloring.
  Proof.
    intros colors coloring unused_colors (H₁ & H₂ & H₃).
    assumption.
  Defined.

  Definition invariant_cons_up_nil : forall (owner : Owner.t) (tail : list (Opcode * Owner.t)) (colors : nat) (coloring : M.t nat), invariant ((Up, owner) :: tail) colors coloring [] -> invariant tail (S colors) (M.add owner colors coloring) [].
  Proof.
    intros owner tail colors coloring (H₁ & H₂ & H₃).
    split.
      apply Correct_add_new with (1 := H₁).
      intros In_owner_coloring.
      apply H₂, Forall_inv in In_owner_coloring as [[=]| eq].
      now apply eq.
    split.
    (*
      intros owner'.
      rewrite add_in_iff, H₂, Forall_iff.
    *)
      intros owner' In_owner'.
      specialize (H₂ owner').
      apply add_in_iff in In_owner' as [eq| In_owner'].
        contradict eq.
        admit.
      now apply Forall_inv_tail with (Up, owner), H₂.
    constructor.
  Admitted.

  Definition invariant_cons_up_cons : forall (owner : Owner.t) (tail : list (Opcode * Owner.t)) (colors : nat) (coloring : M.t nat) (u₀ : nat) (x₀ : list nat), invariant ((Up, owner) :: tail) colors coloring (u₀ :: x₀) -> invariant tail colors (M.add owner u₀ coloring) x₀.
  Proof.
  Admitted.

  Definition invariant_cons_down : forall (owner : Owner.t) (tail : list (Opcode * Owner.t)) (colors : nat) (coloring : M.t nat) (unused_colors : list nat), invariant ((Down, owner) :: tail) colors coloring unused_colors -> forall color : nat, M.MapsTo owner color coloring -> invariant tail colors coloring (color :: unused_colors).
  Proof.
  Admitted.
*)
  Definition regular_correct_invariant : forall (instructions : list (Opcode * Owner.t)) (colors : nat) (coloring : M.t nat) (unused_colors : list nat), invariant instructions colors coloring unused_colors -> Is (fun H => Correct (fst H) (snd H)) True (regular instructions colors coloring unused_colors).
  Proof.
    intros instructions.
    induction instructions as [| [[|] owner] tail IHtail]; intros colors coloring unused_colors invariant; simpl.
        exact (@invariant_nil colors coloring unused_colors invariant).
      destruct unused_colors as [| u₀ x₀].
        specialize (IHtail (S colors) (M.add owner colors coloring) []).
        now apply IHtail, invariant_cons_up_nil.
      specialize (IHtail colors (M.add owner u₀ coloring) x₀).
      now apply IHtail, invariant_cons_up_cons.
    destruct (M.find owner coloring) as [color|] eqn: find.
      specialize (IHtail colors coloring (color :: unused_colors)).
      apply M.find_2 in find.
      apply IHtail.
      exact (@invariant_cons_down owner tail colors coloring unused_colors invariant color find).
    constructor.
  Defined.
(*
  Definition regular_correct : forall (instructions : list (Opcode * Owner.t)) (colors : nat) (coloring : M.t nat) (unused_colors : list nat), Correct colors coloring -> (forall owner : Owner.t, M.In owner coloring <-> Forall (fun H => fst H = Down \/ ~ Owner.eq (snd H) owner) instructions) -> Forall (fun color => exists owner : Owner.t, M.MapsTo owner color coloring) unused_colors -> Is (fun H => Correct (fst H) (snd H)) True (regular instructions colors coloring unused_colors).
  Proof.
    intros instructions.
    induction instructions as [| [opcode owner] tail IHtail]; intros colors coloring unused_colors H₁ H₂ H₃.
      assumption.
    destruct opcode as [|].
      simpl.
      destruct unused_colors as [| u₀ x₀].
        specialize (IHtail (S colors) (M.add owner colors coloring) []).
        apply IHtail.
            apply Correct_add_new.
              assumption.
            specialize (H₂ owner).
            rewrite H₂.
            intros H.
            apply Forall_inv in H.
            destruct H.
              inversion H.
            now apply H.
          intros owner'.
          rewrite add_in_iff.
          rewrite H₂.
          rewrite Forall_iff.
          assert ((fst (Up, owner) = Down \/ ~ Owner.eq (snd (Up, owner)) owner') <-> ~ Owner.eq (snd (Up, owner)) owner') as ->.
            firstorder.
            inversion H.
            firstorder.
          simpl.
          split.
            intros [eq| In].
              specialize (H₂ owner').
              apply Forall_inv_tail with (Up, owner).
              apply H₂.
              rewrite <- eq.
              admit.
            now apply H₂, Forall_inv_tail in In.
          intros G.
          destruct (Owner.eq_dec owner owner') as [eq| neq]; [left| right].
            assumption.
          apply H₂.
          constructor.
            now right.
          assumption.
          constructor.
        specialize (IHtail colors (M.add owner colors coloring) x₀).
          constructor.
          simpl.
          assumption.
            now left.
          
            
          rewrite Forall_iff.
          
          Search (M.In _ (M.add _ _ _)).
        apply 
        simpl.
      admit.
    simpl in *.
    destruct (M.find owner coloring) eqn: e; simpl.
      apply IHtail.
          assumption.
        intros owner'.
        transitivity (Forall (fun H : Opcode * Owner.t => fst H = Down \/ ~ Owner.eq (snd H) owner')
       ((Down, owner) :: tail)).
          apply H₂.
        split; intros H.
          now apply Forall_inv_tail in H.
        now constructor; [left|].
      constructor; [| assumption].
      exists owner.
      now apply M.find_2.
    constructor.
  Defined.
*)
  Definition padded (instructions : list (Opcode * Owner.t)) : option (nat * M.t nat) :=
    regular instructions 0 (M.empty _) [].


End Coloring.
End Test2.

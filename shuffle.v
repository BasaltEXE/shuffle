Set Implicit Arguments.

Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.

Require MSetInterface OrdersFacts OrdersLists.
Require Coq.MSets.MSetFacts Coq.MSets.MSetProperties.
Require Coq.FSets.FMapInterface Coq.FSets.FMapFacts.

Require Import Coq.Classes.RelationClasses.


Require Coq.Structures.Equalities Coq.Structures.EqualitiesFacts.
Require Coq.Structures.Orders Coq.Structures.OrdersAlt Coq.Structures.OrdersFacts.

Require Import  Coq.Classes.Morphisms_Prop.

Import ListNotations.

Import Coq.Structures.Equalities Coq.Structures.EqualitiesFacts.
Import Coq.Structures.Orders Coq.Structures.OrdersAlt Coq.Structures.OrdersFacts.

Require Import FunInd.

Search nth.

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


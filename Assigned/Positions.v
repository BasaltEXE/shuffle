Set Implicit Arguments.

Require Import
  Coq.Structures.Equalities
  Coq.Lists.List
  Coq.Lists.SetoidList
  Coq.Sorting.Sorted.

Import
  ListNotations.

Require
  Coq.FSets.FMapFacts.

Require
  Shuffle.Misc
  Shuffle.List.

Import
  Misc(bind, ret).

Module Card (Key Owner : DecidableTypeBoth) <: DecidableType.
  Inductive Card :
    Type :=
    | Talon : Key.t -> Card
    | Assigned : Owner.t -> Card.

  Definition t :=
    Card.

  Definition eq : t -> t -> Prop :=
    fun self other =>
    match self, other with
    | Talon self_key, Talon other_key => Key.eq self_key other_key
    | Assigned self_owner, Assigned other_owner => Owner.eq self_owner other_owner
    | _, _ => False
    end.

  Add Parametric Morphism : Talon
    with signature Key.eq ==> eq as Talon_morphism.
  Proof.
    now intros k k' k_eq_k'.
  Qed.

  Add Parametric Morphism : Assigned
    with signature Owner.eq ==> eq as Assigned_morphism.
  Proof.
    now intros p p' p_eq_p'.
  Qed.

  Section Properties.
    Variables
      (x_key y_key : Key.t)
      (x_owner y_owner : Owner.t).

    Lemma Talon_Talon_iff :
      eq (Talon x_key) (Talon y_key) <->
      Key.eq x_key y_key.
    Proof.
      reflexivity.
    Qed.

    Lemma Assigned_Talon_iff :
      eq (Assigned x_owner) (Talon y_key) <->
      False.
    Proof.
      reflexivity.
    Qed.

    Lemma Talon_Assigned_iff :
      eq (Talon x_key) (Assigned y_owner) <->
      False.
    Proof.
      reflexivity.
    Qed.

    Lemma Assigned_Assigned_iff :
      eq (Assigned x_owner) (Assigned y_owner) <->
      Owner.eq x_owner y_owner.
    Proof.
      reflexivity.
    Qed.
  End Properties.

  Instance eq_equiv : Equivalence eq.
  Proof.
    split.
        intros card.
        destruct card as [key| owner]; simpl; reflexivity.
      intros [x_key| x_owner] [y_key| y_owner] x_eq_y; now simpl.
    intros [x_key| x_owner] [y_key| y_owner] [z_key| z_owner] x_eq_y y_eq_z;
      simpl; try contradiction.
      now transitivity y_key.
    now transitivity y_owner.
  Defined.

  Definition eq_dec :
    forall
    x y : t,
    {eq x y} +
    {~ eq x y}.
  Proof.
    intros x y.
    destruct x as [x_key| x_owner], y as [y_key| y_owner].
          apply Key.eq_dec.
        now right.
      now right.
    apply Owner.eq_dec.
  Defined.
End Card.

Module Make (Key Owner : DecidableTypeBoth) (Map : FMapInterface.WSfun Owner).
  Module Map_Facts := FMapFacts.WFacts_fun Owner Map.

  Module Card := Card Key Owner.

  Module RNthA := List.RFromNth Card.
  Module EqA := List.FromEqListA Card.
  Module RNthA_Facts := List.RNthAFactsOn Card EqA RNthA.

  Module State.
    Record t :
      Type :=
      new {
        index : nat;
        owner_to_indices : Map.t (list nat);
      }.

    Notation MapsTo
      s
      owner
      indices :=
      (Map.MapsTo owner indices s.(owner_to_indices)).

    Notation Contains
      s
      owner :=
      (Map.In owner s.(owner_to_indices)).

    Notation initial_state :=
      {|
        index := 0;
        owner_to_indices := Map.empty (list nat);
      |}.

    Notation talon
      s :=
      {|
        index := S s.(index);
        owner_to_indices := s.(owner_to_indices)
      |}.

    Notation assigned_mapsto
      s
      owner
      indices :=
      {|
        index := S s.(index);
        owner_to_indices :=
        Map.add
          owner
          (s.(index) :: indices)
          s.(owner_to_indices);
      |}.

    Notation assigned_not_in
      s
      owner
      :=
      {|
        index := S s.(index);
        owner_to_indices :=
        Map.add
          owner
          [s.(index)]
          s.(owner_to_indices);
      |}.
  End State.

  Module Transition.
    Inductive t :
      State.t ->
      Card.t ->
      State.t ->
      Prop :=
      | Talon :
        forall
        (s₁ : State.t)
        (key : Key.t),
        t s₁ (Card.Talon key) (State.talon s₁)
      | Assigned_MapsTo :
        forall
        (s₁ : State.t)
        (owner : Owner.t)
        (indices : list nat),
        State.MapsTo s₁ owner indices ->
        t s₁ (Card.Assigned owner) (State.assigned_mapsto s₁ owner indices)
      | Assigned_not_In :
        forall
        (s₁ : State.t)
        (owner : Owner.t),
        ~ State.Contains s₁ owner ->
        t s₁ (Card.Assigned owner) (State.assigned_not_in s₁ owner).

    Lemma serial :
      forall
      (s₁ : State.t)
      (u₀ : Card.t),
      exists
      s₀ : State.t,
      t s₁ u₀ s₀.
    Proof.
      intros s₁ [key| owner].
        exists (State.talon s₁); constructor.
      destruct (Map.find owner s₁.(State.owner_to_indices)) as
        [indices|] eqn: find.
        now exists (State.assigned_mapsto s₁ owner indices); constructor; apply Map.find_2.
      now exists (State.assigned_not_in s₁ owner); constructor;
      apply Map_Facts.not_find_in_iff.
    Qed.
  End Transition.

  Module Graph.
    Inductive t
      (s : State.t) :
      list Card.t ->
      State.t ->
      Prop :=
      | Nil :
        t s [] s
      | Cons :
        forall
        (u₀ : Card.t)
        (x₀ : list Card.t)
        (t₀ t₁ : State.t),
        t s x₀ t₁ ->
        Transition.t t₁ u₀ t₀ ->
        t s (u₀ :: x₀) t₀.

    Lemma nil_iff :
      forall
      s t : State.t,
      Graph.t s [] t <->
      s = t.
    Proof.
      intros s t; split.
        now inversion 1.
      intros <-; constructor.
    Qed.

    Lemma cons_iff :
      forall
      (u₀ : Card.t)
      (x₀ : list Card.t)
      (s t₀ : State.t),
      Graph.t s (u₀ :: x₀) t₀ <->
      exists
      t₁ : State.t,
      Graph.t s x₀ t₁ /\
      Transition.t t₁ u₀ t₀.
    Proof.
      intros u₀ x₀ s t₀; split.
        inversion_clear 1 as [| ? ? ? t₁ Graph_s_t₁ Transition_t₁_t₀ ].
        now exists t₁.
      intros (t₁ & Graph_s_t₁ & Transition_t₁_t₀).
      now constructor 2 with t₁.
    Qed.

    Lemma app_iff :
      forall
      (x y : list Card.t)
      (s u : State.t),
      Graph.t s (x ++ y) u <->
      exists
      t : State.t,
      Graph.t s y t /\
      Graph.t t x u.
    Proof.
      intros x y s; move x after s.
      induction x as [| u₀ x₀ IHx₀]; intros u.
        split.
          intros Graph_s_u.
          exists u; split; [assumption| constructor].
        intros (t & Graph_s_t & Graph_t_u).
        now apply nil_iff in Graph_t_u as ->.
      split.
        intros Graph_s_u; change (Graph.t s (u₀ :: x₀ ++ y) u) in Graph_s_u.
        apply cons_iff in Graph_s_u as (u' & Graph_s_u' & Transition_u'_u).
        apply IHx₀ in Graph_s_u' as (t & Graph_s_t & Graph_t_u').
        now exists t; split; [| constructor 2 with u'].
      intros (t & Graph_s_t & Graph_t_u).
      apply cons_iff in Graph_t_u as (u' & Graph_t_u' & Transition_u'_u).
      enough (Graph.t s (x₀ ++ y) u') by (now constructor 2 with u').
      now apply IHx₀; exists t.
    Qed.

    Lemma serial :
      forall
      (x : list Card.t)
      (s : State.t),
      exists
      t : State.t,
      Graph.t s x t.
    Proof.
      intros x s.
      induction x as [| u₀ x₀ (t₁ & Graph_s_t₁)].
        exists s; constructor.
      specialize Transition.serial with t₁ u₀ as (t₀ & Transition_t₁_t₀).
      now exists t₀; constructor 2 with t₁.
    Qed.
  End Graph.

  Module Ok.
    Record t
      (x : list Card.t)
      (s : State.t) :
      Prop :=
      new {
        length :
          s.(State.index) = length x;
        contains :
          forall
          owner : Owner.t,
          State.Contains s owner <->
          InA Card.eq (Card.Assigned owner) x;
        sorted :
          forall
          (owner : Owner.t)
          (indices : list nat),
          State.MapsTo s owner indices ->
          LocallySorted Peano.gt indices;
        positions :
          forall
          (owner : Owner.t)
          (indices : list nat)
          (offset : nat),
          State.MapsTo s owner indices ->
          In offset indices <->
          RNthA.t (Card.Assigned owner) x offset;
      }.

    Lemma initial_state :
      t [] State.initial_state.
    Proof.
      constructor; simpl.
            reflexivity.
          now intros owner; rewrite Map_Facts.empty_in_iff, InA_nil.
        intros owner indices owner_to_indices.
        now apply Map_Facts.empty_mapsto_iff in owner_to_indices.
      intros owner indices subtrahend owner_to_indices.
      now apply Map_Facts.empty_mapsto_iff in owner_to_indices.
    Qed.

    Lemma cons_iff :
      forall
      (v u₀ : Card.t)
      (x₀ : list Card.t)
      (n : nat),
      RNthA.t v (u₀ :: x₀) n <->
      n = Datatypes.length x₀ /\ Card.eq v u₀ \/
      RNthA.t v x₀ n.
    Proof.
      intros v u₀ x₀ n.
      enough (RNthA.t v x₀ n -> n <> Datatypes.length x₀)
        by (rewrite RNthA_Facts.cons_iff; tauto).
      intros n_to_v.
      now apply PeanoNat.Nat.lt_neq, RNthA_Facts.lt_iff; exists v.
    Qed.

    Lemma talon :
      forall
      (x₀ : list Card.t)
      (s₁ : State.t)
      (key : Key.t),
      t x₀ s₁ ->
      t (Card.Talon key :: x₀) (State.talon s₁).
    Proof.
      intros x₀ (index & owner_to_indices) key Ok_s₁.
      constructor.
            apply eq_S, Ok_s₁.(length).
          intros owner.
          rewrite Ok_s₁.(contains), InA_cons; simpl; tauto.
        intros owner indices owner_to_indices'.
        now apply Ok_s₁.(sorted) with owner.
      intros owner indices offset MapsTo_owner_indices.
      rewrite cons_iff, Ok_s₁.(positions) with (1 := MapsTo_owner_indices); simpl; tauto.
    Defined.

    Lemma assigned_mapsto :
      forall
      (p₀ : Owner.t)
      (x₀ : list Card.t)
      (s₁ : State.t)
      (indices₀ : list nat),
      State.MapsTo s₁ p₀ indices₀ ->
      t x₀ s₁ ->
      t (Card.Assigned p₀ :: x₀) (State.assigned_mapsto s₁ p₀ indices₀).
    Proof with (simpl; firstorder).
      intros p₀ x₀ (index & owner_to_indices) indices₀ MapsTo_p₀_indices₀ Ok_s₁.
      constructor.
            apply eq_S, Ok_s₁.(length).
          intros owner; simpl.
          rewrite Map_Facts.add_in_iff, Ok_s₁.(contains), InA_cons...
        intros owner indices MapsTo_owner_indices.
        apply Map_Facts.add_mapsto_iff in MapsTo_owner_indices as [
          (_ & <-)|
        (_ & MapsTo_owner_indices)].
          destruct indices₀ as [| index₀ indices₀]; constructor.
            now apply Ok_s₁.(sorted) with p₀.
          rewrite Ok_s₁.(length).
          apply RNthA_Facts.lt_iff; exists (Card.Assigned p₀).
          now apply Ok_s₁.(positions) with (1 := MapsTo_p₀_indices₀); left.
        now apply Ok_s₁.(sorted) with owner.
      intros owner indices offset MapsTo_owner_indices;
      rewrite cons_iff.
      apply Map_Facts.add_mapsto_iff in MapsTo_owner_indices as [
        (<- & <-)|
      (p₀_neq_owner & MapsTo_owner_indices)].
        simpl; rewrite Ok_s₁.(positions) with (1 := MapsTo_p₀_indices₀).
        setoid_rewrite <- Ok_s₁.(length)...
      setoid_replace (Owner.eq owner p₀) with (Owner.eq p₀ owner) by firstorder.
      rewrite Ok_s₁.(positions) with (1 := MapsTo_owner_indices); tauto.
    Qed.

    Lemma assigned_not_in :
      forall
      (p₀ : Owner.t)
      (x₀ : list Card.t)
      (s₁ : State.t),
      ~ Map.In p₀ s₁.(State.owner_to_indices) ->
      t x₀ s₁ ->
      t (Card.Assigned p₀ :: x₀) (State.assigned_not_in s₁ p₀).
    Proof with (simpl; firstorder).
      intros p₀ x₀ (index & owner_to_indices) not_In_p₀ Ok_s₁.
      constructor.
            apply eq_S, Ok_s₁.(length).
          intros owner; simpl.
          rewrite Map_Facts.add_in_iff, Ok_s₁.(contains), InA_cons...
        intros owner indices MapsTo_owner_indices.
        apply Map_Facts.add_mapsto_iff in MapsTo_owner_indices as [
          (_ & <-)|
        (_ & MapsTo_owner_indices)].
          constructor.
        now apply Ok_s₁.(sorted) with owner.
      intros owner indices offset MapsTo_owner_indices;
      rewrite cons_iff.
      apply Map_Facts.add_mapsto_iff in MapsTo_owner_indices as [
        (p₀_eq_owner & <-)|
      (p₀_neq_owner & MapsTo_owner_indices)].
        setoid_rewrite <- Ok_s₁.(length); simpl.
        enough (~ RNthA.t (Card.Assigned owner) x₀ offset) by firstorder.
        contradict not_In_p₀.
        apply Ok_s₁.(contains),  RNthA_Facts.InA_iff.
        now exists offset; rewrite p₀_eq_owner.
      setoid_replace (Owner.eq owner p₀) with (Owner.eq p₀ owner) by firstorder.
      rewrite <- Ok_s₁.(positions) with (1 := MapsTo_owner_indices); tauto.
    Qed.

    Lemma transition :
      forall
      (u₀ : Card.t)
      (x₀ : list Card.t)
      (s₀ s₁ : State.t),
      Transition.t s₁ u₀ s₀ ->
      t x₀ s₁ ->
      t (u₀ :: x₀) s₀.
    Proof.
      intros u₀ x₀ s₀ s₁ Transition_s₁_s₀.
      destruct Transition_s₁_s₀ as [
          s₁ key |
        s₁ p₀ indices₀ MapsTo_p₀_indices₀|
      s₁ p₀ not_In_p₀];
      intros Ok_s₁.
          now apply talon.
        now apply assigned_mapsto.
      now apply assigned_not_in.
    Qed.

    Lemma graph :
      forall
      (x : list Card.t)
      (s t : State.t),
      Graph.t s x t ->
      Ok.t [] s ->
      Ok.t x t.
    Proof.
      intros x s t Graph_s_t Ok_s.
      now induction Graph_s_t as
        [| u₀ x₀ t₀ t₁ Graph_s_t₁ IHs_t₁ Transition_t₁_t₀];
        [| apply transition with t₁].
    Qed.
  End Ok.

  Lemma spec :
    forall
    x : list Card.t,
    exists
    t : State.t,
    Graph.t State.initial_state x t /\
    (forall
    owner : Owner.t,
    InA Card.eq (Card.Assigned owner) x <->
    State.Contains t owner) /\
    (forall
    (owner : Owner.t)
    (indices : list nat),
    State.MapsTo t owner indices ->
    LocallySorted Peano.gt indices /\
    (forall
    offset : nat,
    In offset indices <->
    RNthA.t (Card.Assigned owner) x offset)).
  Proof with auto.
    intros x; pose (s := State.initial_state).
    specialize Graph.serial with x s as (t & Graph_s_t).
    assert (Ok_s : Ok.t [] s) by apply Ok.initial_state.
    pose (Ok_t := Ok.graph Graph_s_t Ok_s).
    exists t; split; [assumption|].
    split.
      intros owner; symmetry; apply Ok_t.(Ok.contains).
    intros owner indices owner_to_indices.
    split.
      now apply Ok_t.(Ok.sorted) with owner.
    intros offset.
    now apply Ok_t.(Ok.positions).
  Qed.

  Fixpoint generate_body
    (cards : list Card.t)
    (state : State.t) :
    State.t :=
    match cards with
    | [] => state
    | Card.Talon _ :: cards =>
      let state₁ := generate_body cards state in
      State.talon state₁
    | Card.Assigned owner :: cards =>
      let state₁ := generate_body cards state in
      match Map.find owner state₁.(State.owner_to_indices) with
      | Some indices => State.assigned_mapsto state₁ owner indices
      | None => State.assigned_not_in state₁ owner
      end
    end.

  Definition generate
    (cards : list Card.t) :
    Map.t (list nat) :=
    (generate_body cards State.initial_state).(State.owner_to_indices).

  Lemma generate_body_spec :
    forall
    (cards : list Card.t)
    (s t : State.t),
    Graph.t s cards t ->
    generate_body cards s = t.
  Proof.
    intros x s t Graph_s_t.
    induction Graph_s_t as [| u₀ x₀ t₀ t₁ Graph_s_t₁ IHs_t₁ Transition_t₁_t₀].
      reflexivity.
    destruct Transition_t₁_t₀ as [
        t₁ key|
      t₁ p₀ indices₀ MapsTo_p₀_indices₀|
    t₁ p₀ not_In_p₀]; simpl in *; rewrite IHs_t₁.
        reflexivity.
      now apply Map.find_1 in MapsTo_p₀_indices₀ as ->.
    now apply Map_Facts.not_find_in_iff in not_In_p₀ as ->.
  Qed.

  Lemma generate_spec :
    forall
    cards : list Card.t,
    let positions := generate cards in
    (forall
    owner : Owner.t,
    InA Card.eq (Card.Assigned owner) cards <->
    Map.In owner positions) /\
    (forall
    (owner : Owner.t)
    (indices : list nat),
    Map.MapsTo owner indices positions ->
    LocallySorted Peano.gt indices /\
    (forall
    offset : nat,
    In offset indices <->
    RNthA.t (Card.Assigned owner) cards offset)).
  Proof.
    intros cards positions.
    specialize spec with cards as
      (t & Graph_s_t & contains_sorted_positions).
    enough (positions = t.(State.owner_to_indices)) as -> by assumption.
    now unfold positions, generate;
    rewrite generate_body_spec with (1 := Graph_s_t).
  Qed.
End Make.

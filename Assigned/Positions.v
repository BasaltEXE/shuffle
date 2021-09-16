Set Implicit Arguments.

Require Import
  Coq.Structures.Equalities
  Coq.Lists.List
  Coq.Lists.SetoidList
  Coq.Sorting.Sorted
  Coq.Classes.RelationClasses
  Coq.Classes.Morphisms_Prop.

Import
  ListNotations.

Require
  Coq.FSets.FMapFacts.

Require
  Shuffle.Misc
  Shuffle.List.

Require Import
  Shuffle.TransitionSystem.

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

  Definition L :
    Type :=
    Card.t.

  Instance Eq_L :
    Setoid.Eq L :=
    Card.eq.

  Program Definition Signature_L :
    Label.Signature L :=
    {|
      Label.Ok x :=
        True;
    |}.
  Next Obligation.
    intros x x' x_eq_x'; reflexivity.
  Qed.

  Program Instance Label_Theory_L :
    Label.Theory Signature_L.

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

    Lemma Raw :
      forall
      (x : list Card.t)
      (s : State.t),
      t x s <->
      s.(State.index) = List.length x /\
      (forall
      owner : Owner.t,
      State.Contains s owner <->
      InA Card.eq (Card.Assigned owner) x) /\
      (forall
      (owner : Owner.t)
      (indices : list nat),
      State.MapsTo s owner indices ->
      LocallySorted Peano.gt indices) /\
      (forall
      (owner : Owner.t)
      (indices : list nat)
      (offset : nat),
      State.MapsTo s owner indices ->
      In offset indices <->
      RNthA.t (Card.Assigned owner) x offset).
    Proof.
      intros x s; split.
        now intros [length_x contains_s sorted_s positions_s].
      intros (length_x & contains_s & sorted_s & positions_s).
      now constructor.
    Qed.

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
  End Ok.

  Instance Eq_State :
    Setoid.Eq State.t :=
    fun s s' : State.t =>
      s.(State.index) = s'.(State.index) /\
      Map.Equal s.(State.owner_to_indices) s'.(State.owner_to_indices).

  Program Instance Signature_L_S
    {Setoid_L : TransitionSystem.Setoid.Setoid L} :
    Algebraic.Signature L State.t :=
    {|
      Algebraic.init :=
        State.initial_state;
      Algebraic.f s u :=
        match u with
        | Card.Talon _ =>
          Some (
          State.talon s)
        | Card.Assigned owner =>
          Some (
          match Map.find owner s.(State.owner_to_indices) with
          | Some indices => State.assigned_mapsto s owner indices
          | None => State.assigned_not_in s owner
          end)
        end;
      Algebraic.Ok :=
        Ok.t;
    |}.
  Next Obligation.
    intros s s' s_eq_s' [k| p] [k'| p'] u_eq_u'; constructor.
          change (Key.eq k k') in u_eq_u'; split.
            simpl; f_equal.
            apply s_eq_s'.
          apply s_eq_s'.
        inversion u_eq_u'.
      inversion u_eq_u'.
    destruct s_eq_s' as (index_eq_index' & positions_eq_positions').
    change (Owner.eq p p') in u_eq_u'; simpl in *.
    rewrite positions_eq_positions'.
    destruct (Map.find p (State.owner_to_indices s')) as [indices'|] eqn: e; simpl in *;  rewrite u_eq_u' in e; rewrite e; simpl.
      split; simpl.
        now f_equal.
      now rewrite u_eq_u', index_eq_index', positions_eq_positions'.
    split; simpl.
      now f_equal.
    now rewrite u_eq_u', index_eq_index', positions_eq_positions'.
  Qed.
  Next Obligation.
    intros x x' x_eq_x' s s' (index_eq_index' & positions_eq_positions').
    rewrite 2!Ok.Raw.
    repeat try apply and_iff_morphism.
          now rewrite x_eq_x', index_eq_index'.
        apply all_iff_morphism; intros owner.
        now rewrite x_eq_x', positions_eq_positions'.
      apply all_iff_morphism; intros owner;
      apply all_iff_morphism; intros indices.
      now rewrite positions_eq_positions'.
    apply all_iff_morphism; intros owner;
    apply all_iff_morphism; intros indices;
    apply all_iff_morphism; intros offset.
    now rewrite x_eq_x', positions_eq_positions'.
  Qed.

  Instance Theory_L_S
    {Setoid_L : TransitionSystem.Setoid.Setoid L} :
    Algebraic.Theory Signature_L Signature_L_S.
  Proof.
    split.
      apply Ok.initial_state.
    intros [k₀| p₀] x₀ s _ Ok_x₀_s.
      exists (State.talon s); split.
        simpl.
        constructor.
        now constructor.
      now apply Ok.talon.
    destruct (Map.find p₀ s.(State.owner_to_indices)) as [indices|] eqn: e.
      exists (State.assigned_mapsto s p₀ indices); split.
        simpl; rewrite e.
        now constructor.
      now apply Ok.assigned_mapsto; [apply Map_Facts.find_mapsto_iff|].
    exists (State.assigned_not_in s p₀); split.
      simpl; rewrite e.
      now constructor.
    now apply Ok.assigned_not_in; [apply Map_Facts.not_find_in_iff|].
  Qed.

  Notation Graph :=
    (TransitionSystem.Relational.Path.R (Algebraic.to_Relational_Signature Signature_L_S)).

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

  Lemma generate_body_eq_try_fold
    {Setoid_L : Setoid.Setoid L} :
    forall
    (x : list Card.t)
    (s : State.t),
    Setoid.try_fold _ _
      s
      Signature_L_S.(Algebraic.f) x = Some
        (generate_body x s).
  Proof.
    induction x as [| u₀ x₀ IHx₀].
      reflexivity.
    intros s.
    simpl.
    rewrite IHx₀.
    simpl.
    destruct u₀; try reflexivity.
    destruct ( Map.find t (State.owner_to_indices (generate_body x₀ s))).
    reflexivity.
    reflexivity.
  Qed.

  Definition generate
    (cards : list Card.t) :
    Map.t (list nat) :=
    (generate_body cards State.initial_state).(State.owner_to_indices).

  #[local]
  Hint Resolve Algebraic.to_Relational_Theory : typeclass_instances.
  #[local]
  Hint Resolve Algebraic.to_Relational_Path_Theory : typeclass_instances.

  Lemma generate_spec
    {Setoid_L : Setoid.Setoid L}
    {Setoid_S : Setoid.Setoid State.t} :
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
    specialize (Relational.Path.executable_Initial Signature_L (Algebraic.to_Relational_Signature Signature_L_S) (Algebraic.to_Relational_Path_Signature Signature_L_S) cards State.initial_state I) as (t & Path_init_t & Ok_cards_t).
      simpl; reflexivity.
    change (Setoid.eq (Setoid.try_fold _ _ Signature_L_S.(Algebraic.init) Signature_L_S.(Algebraic.f) cards) (Some t)) in Path_init_t.
    rewrite generate_body_eq_try_fold in Path_init_t.
     change positions with ((generate_body cards State.initial_state).(State.owner_to_indices)).
    inversion_clear Path_init_t.
    destruct H as (index_eq_index' & positions_eq_positions').
    setoid_rewrite positions_eq_positions'.
    split.
    symmetry.
    apply Ok_cards_t.(Ok.contains).
  intros owner indices owner_to_indices; split.
    now apply Ok_cards_t.(Ok.sorted) with owner.
  intros offset.
  now apply Ok_cards_t.(Ok.positions).
  Qed.
End Make.

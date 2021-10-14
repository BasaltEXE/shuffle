Set Implicit Arguments.

Require Import
  Coq.Structures.Equalities
  Coq.Lists.List
  Coq.Lists.SetoidList
  Coq.Sorting.Sorted
  Lia.

Import
  ListNotations.

Require
  Coq.FSets.FMapFacts.

Require
  Shuffle.Misc
  Shuffle.List
  Shuffle.Assigned.Instructions.

Require Import
  Shuffle.TransitionSystem.

Import
  Misc(bind, ret)
  Setoid(if_then_else).

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
  Module Instructions := Instructions.Make Owner.
  Module Instruction := Instructions.Instruction.

  Module RNthA := List.RFromNth Card.
  Module EqA := List.FromEqListA Card.

  Module EqA_Facts := List.EqAFactsOn Card EqA.
  Module RNthA_Facts := List.RNthAFactsOn Card EqA RNthA.

  Import Instructions.Notations.

  Lemma Functional_RNthA :
    forall
    (v v' : Card.t)
    (x : list Card.t)
    (n : nat),
    RNthA.t v x n ->
    RNthA.t v' x n ->
    Card.eq v v'.
  Proof.
    intros v v' x n.
    rewrite <- 2!RNthA_Facts.split_iff.
    intros (y & z & e & f) (y' & z' & e' & f').
    enough (EqA.eq (v :: z) (v' :: z')).
      now apply EqA.eq_cons_cons_iff with z z'.
    apply EqA_Facts.eq_app_app_iff with y y'.
      right; simpl; now rewrite f, f'.
    now rewrite <- e, <- e'.
  Qed.

  Lemma last_cons :
    forall
    (A : Type)
    (v u₀ : A)
    (x₀ : list A),
    last (u₀ :: x₀) v = last x₀ u₀.
  Proof.
    intros A v u₀ x₀; move x₀ after v; revert v u₀.
    induction x₀ as [| u₁ x₁ IHx₁]; intros v u₀.
      reflexivity.
    change (last (u₁ :: x₁) v = last (u₁ :: x₁) u₀).
    now rewrite 2!IHx₁.
  Qed.

  Definition last_error
    (A : Type)
    (x : list A) :
    option A :=
    match x with
    | [] =>
        None
    | u₀ :: x₀ =>
        Some (last x₀ u₀)
    end.

  Lemma last_error_cons :
    forall
    (A : Type)
    (u₀ u₁ : A)
    (x₁ : list A),
    last_error (u₀ :: u₁ :: x₁) = last_error (u₁ :: x₁).
  Proof.
    intros A u₀ u₁ x₁.
    change (Some (last (u₁ :: x₁) u₀) = last_error (u₁ :: x₁)).
    now rewrite last_cons.
  Qed.

  Notation Last
    v
    x :=
    (last_error x = Some v).

  Lemma In_Last :
    forall
    (A : Type)
    (v : A)
    (x : list A),
    Last v x ->
    List.In v x.
  Proof.
    intros A v x.
    induction x as [| u₀ [| u₁ x₁] IHx₀]; intros [=Last_v_x].
      now left.
    right; change (last (u₁ :: x₁) u₀ = v) in Last_v_x.
    apply IHx₀; change (Some (last x₁ u₁) = Some v); f_equal.
    now rewrite <- last_cons with (v := u₀).
  Qed.

  Lemma Functional_Last :
    forall
    (A : Type)
    (v w : A)
    (x : list A),
    Last v x ->
    Last w x ->
    v = w.
  Proof.
    intros A v w x.
    induction x as [| u₀ [| u₁ x₁] IHx₀]; intros Last_v_x Last_w_x.
        inversion Last_v_x.
      inversion Last_v_x.
      inversion Last_w_x.
      now transitivity u₀.
    rewrite last_error_cons in Last_v_x, Last_w_x.
    now apply IHx₀.
  Qed.

  Notation Head
    v
    x :=
    (hd_error x = Some v).

  Lemma In_Head :
    forall
    (A : Type)
    (v : A)
    (x : list A),
    Head v x ->
    List.In v x.
  Proof.
    intros A v [| u₀ x₀] [=->]; now left.
  Qed.

  Lemma Functional_Head :
    forall
    (A : Type)
    (v w : A)
    (x : list A),
    Head v x ->
    Head w x ->
    v = w.
  Proof.
    intros A v w x Head_v_x Head_w_x.
    enough (Some v = Some w) as [=] by assumption.
    now transitivity (hd_error x).
  Qed.

  Lemma Sorted_Head_Last :
    forall
    x : list nat,
    LocallySorted Peano.gt x ->
    forall
    head last : nat,
    Head head x ->
    Last last x ->
    head = last \/
    head > last.
  Proof.
    induction 1 as [| u₀| u₀ u₁ x₁ Sorted_x₀ IHx₀ u₀_gt_u₁];
    intros head last [=<-] Last_last_x.
      left; enough (Some u₀ = Some last) as [=] by assumption.
      now transitivity (Some u₀).
    right; unfold gt.
    specialize IHx₀ with u₁ last as [<-|].
          reflexivity.
        now rewrite last_error_cons in Last_last_x.
      assumption.
    now transitivity u₁.
  Qed.

  Lemma cons_Up_iff :
    forall
    (v p₀ : Owner.t)
    (x₀ : Instructions.t),
    In (Down v) (Up p₀ :: x₀) <->
    In (Down v) x₀.
  Proof.
    intros v p₀ x₀; rewrite InA_cons.
    enough (~ Instruction.eq (Down v) (Up p₀)) by tauto.
    now apply Instruction.neq_opcode.
  Qed.

  Lemma cons_Down_iff :
    forall
    (v p₀ : Owner.t)
    (x₀ : Instructions.t),
    In (Down v) (Down p₀ :: x₀) <->
    Owner.eq p₀ v \/ In (Down v) x₀.
  Proof.
    intros v p₀ x₀; rewrite InA_cons.
    rewrite Instruction.eq_opcode by reflexivity.
    firstorder.
  Qed.

  Instance Morphism_Instructions_Ok :
    Proper (eqlistA Instruction.eq ==> iff) Instructions.Ok.
  Proof.
    intros x x' x_eq_x'.
    induction x_eq_x' as
      [| ([|] & p₀) ([|] & p₀') x₀ x₀' u₀_eq_u₀' x₀_eq_x₀' IHx₀_eq_x₀'];
      [reflexivity|..];
    destruct u₀_eq_u₀' as ([=] & p₀_eq_p₀');
    change (Owner.eq p₀ p₀') in p₀_eq_p₀';
    rewrite
      2 ? Instructions.Ok.cons_Up_iff,
      2 ? Instructions.Ok.cons_Down_iff;
    now rewrite IHx₀_eq_x₀', p₀_eq_p₀', x₀_eq_x₀'.
  Qed.

  Module Indices.
    Record t
      (cards : list Card.t)
      (owner_to_indices : Map.t (list nat)) :
      Prop :=
      new
      {
        contains :
          forall
          owner : Owner.t,
          Map.In owner owner_to_indices <->
          InA Card.eq (Card.Assigned owner) cards;
        sorted :
          forall
          (owner : Owner.t)
          (indices : list nat),
          Map.MapsTo owner indices owner_to_indices ->
          LocallySorted Peano.gt indices;
        positions :
          forall
          (owner : Owner.t)
          (indices : list nat)
          (offset : nat),
          Map.MapsTo owner indices owner_to_indices ->
          List.In offset indices <->
          RNthA.t (Card.Assigned owner) cards offset;
      }.

    Instance Morphism :
      Proper (eqlistA Card.eq ==> Map.Equal ==> iff) t.
    Proof.
      intros x x' x_eq_x' m m' m_eq_m'; split;
      intros [contains sorted positions].
        now constructor;
        setoid_rewrite <- m_eq_m'; try setoid_rewrite <- x_eq_x'.
      now constructor;
      setoid_rewrite m_eq_m'; try setoid_rewrite x_eq_x'.
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

    Lemma initial_state :
      t [] (Map.empty (list nat)).
    Proof.
      constructor; simpl.
          now intros owner; rewrite Map_Facts.empty_in_iff, InA_nil.
        intros owner indices owner_to_indices.
        now apply Map_Facts.empty_mapsto_iff in owner_to_indices.
      intros owner indices subtrahend owner_to_indices.
      now apply Map_Facts.empty_mapsto_iff in owner_to_indices.
    Qed.

    Section Indices.
      Variables
        (k₀ : Key.t)
        (p₀ : Owner.t)
        (x₀ : list Card.t)
        (owner_to_indices : Map.t (list nat)).

      Lemma talon :
        t x₀ owner_to_indices ->
        t (Card.Talon k₀ :: x₀) owner_to_indices.
      Proof.
        intros Ok_s₁.
        constructor.
            intros owner.
            rewrite Ok_s₁.(contains), InA_cons; simpl; tauto.
          intros owner indices owner_to_indices'.
          now apply Ok_s₁.(sorted) with owner.
        intros owner indices offset MapsTo_owner_indices.
        rewrite cons_iff, Ok_s₁.(positions) with (1 := MapsTo_owner_indices); simpl; tauto.
      Defined.

      Lemma assigned_mapsto :
        forall
        indices₀ : list nat,
        Map.MapsTo p₀ indices₀ owner_to_indices ->
        t x₀ owner_to_indices ->
        t
          (Card.Assigned p₀ :: x₀)
          (Map.add p₀ (length x₀ :: indices₀) owner_to_indices).
      Proof with (simpl; firstorder).
        intros indices₀ MapsTo_p₀_indices₀ Ok_s₁.
        constructor.
            intros owner; simpl.
            rewrite Map_Facts.add_in_iff, Ok_s₁.(contains), InA_cons...
          intros owner indices MapsTo_owner_indices.
          apply Map_Facts.add_mapsto_iff in MapsTo_owner_indices as [
            (_ & <-)|
          (_ & MapsTo_owner_indices)].
            destruct indices₀ as [| index₀ indices₀]; constructor.
              now apply Ok_s₁.(sorted) with p₀.
            apply RNthA_Facts.lt_iff; exists (Card.Assigned p₀).
            now apply Ok_s₁.(positions) with (1 := MapsTo_p₀_indices₀); left.
          now apply Ok_s₁.(sorted) with owner.
        intros owner indices offset MapsTo_owner_indices;
        rewrite cons_iff.
        apply Map_Facts.add_mapsto_iff in MapsTo_owner_indices as [
          (<- & <-)|
        (p₀_neq_owner & MapsTo_owner_indices)].
          simpl; rewrite Ok_s₁.(positions) with (1 := MapsTo_p₀_indices₀)...
        setoid_replace (Owner.eq owner p₀) with (Owner.eq p₀ owner) by firstorder.
        rewrite Ok_s₁.(positions) with (1 := MapsTo_owner_indices); tauto.
      Qed.

      Lemma assigned_not_in :
        ~ Map.In p₀ owner_to_indices ->
        t x₀ owner_to_indices ->
        t
          (Card.Assigned p₀ :: x₀)
          (Map.add p₀ [length x₀] owner_to_indices).
      Proof with (simpl; firstorder).
        intros not_In_p₀ Ok_s₁.
        constructor.
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
          simpl;
          enough (~ RNthA.t (Card.Assigned owner) x₀ offset) by firstorder.
          contradict not_In_p₀.
          apply Ok_s₁.(contains), RNthA_Facts.InA_iff.
          now exists offset; rewrite p₀_eq_owner.
        setoid_replace (Owner.eq owner p₀) with (Owner.eq p₀ owner) by firstorder.
        rewrite <- Ok_s₁.(positions) with (1 := MapsTo_owner_indices); tauto.
      Qed.
    End Indices.
  End Indices.
  Import Indices(contains, sorted, positions).

  Module Generate.
    Module Label <:
      EqualityType.
      Definition t :
        Type :=
        Card.t.

      Definition eq :
        relation Label.t :=
        Card.eq.

      #[program]
      Instance eq_equiv :
        Equivalence Label.eq.

      #[program]
      Definition Signature :
        Label.Signature Label.eq :=
        {|
          Label.Ok x :=
            True;
        |}.
      Next Obligation.
        intros x x' x_eq_x'; reflexivity.
      Qed.

      #[local, program]
      Instance Theory :
        Label.Theory Label.Signature.
    End Label.

    Module State <:
      EqualityType.
      Record State :
        Type :=
        new {
          index : nat;
          owner_to_indices : Map.t (list nat);
        }.

      Definition t :
        Type :=
        State.

      Definition eq :
        relation State.t :=
        fun s s' : State.t =>
          s.(State.index) = s'.(State.index) /\
          Map.Equal s.(State.owner_to_indices) s'.(State.owner_to_indices).

      Instance eq_equiv :
        Equivalence State.eq.
      Proof.
        split.
            intros x; split; reflexivity.
          intros x y x_eq_y; split; symmetry; apply x_eq_y.
        intros x y z x_eq_y y_eq_z; split.
          transitivity (y.(State.index)).
            apply x_eq_y.
          apply y_eq_z.
        transitivity (y.(State.owner_to_indices)).
          apply x_eq_y.
        apply y_eq_z.
      Qed.

      Instance Morphism_new :
        Proper (Logic.eq ==> Map.Equal ==> State.eq) State.new.
      Proof.
        intros index index' index_eq_index'
          positions positions' positions_eq_positions'; split.
          now rewrite index_eq_index'.
        simpl; now rewrite positions_eq_positions'.
      Qed.

      Instance Morphism_index :
        Proper (State.eq ==> Logic.eq) State.index.
      Proof.
        intros s s' s_eq_s'.
        apply s_eq_s'.
      Qed.

      Instance Morphism_owner_to_indices :
        Proper (State.eq ==> Map.Equal) State.owner_to_indices.
      Proof.
        intros s s' s_eq_s'.
        apply s_eq_s'.
      Qed.

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

      Module Ok.
        Record t
          (x : list Card.t)
          (s : State.t) :
          Prop :=
          new {
            length :
              s.(State.index) = length x;
            indices :
              Indices.t x s.(State.owner_to_indices);
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
          List.In offset indices <->
          RNthA.t (Card.Assigned owner) x offset).
        Proof.
          intros x s; split.
            now intros (length_x & [contains_s sorted_s positions_s]).
          intros (length_x & contains_s & sorted_s & positions_s).
          now constructor.
        Qed.

        Lemma initial_state :
          t [] State.initial_state.
        Proof.
          constructor; simpl.
            reflexivity.
          apply Indices.initial_state.
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
          apply Indices.talon, Ok_s₁.(indices).
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
          now rewrite Ok_s₁.(length);
          apply Indices.assigned_mapsto, Ok_s₁.(indices).
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
          now rewrite Ok_s₁.(length);
          apply Indices.assigned_not_in, Ok_s₁.(indices).
        Qed.
      End Ok.

      Unset Program Cases.
      #[program]
      Definition Signature :
        Algebraic.Signature Label.eq State.eq :=
        {|
          Algebraic.init :=
            State.initial_state;
          Algebraic.f s u :=
            Some
              (match u with
              | Card.Talon _ =>
                  State.talon s
              | Card.Assigned owner =>
                  match Map.find owner s.(State.owner_to_indices) with
                  | Some indices => State.assigned_mapsto s owner indices
                  | None => State.assigned_not_in s owner
                  end
              end);
          Algebraic.Ok :=
            State.Ok.t;
        |}.
      Next Obligation.
        intros s s' s_eq_s' [k| p] [k'| p'] u_eq_u';
        compute in u_eq_u'; try contradiction; constructor.
          now rewrite s_eq_s'.
        rewrite u_eq_u', s_eq_s'.
        destruct (Map.find p' (State.owner_to_indices s')) as [indices'|];
        now rewrite u_eq_u', s_eq_s'.
      Qed.
      Next Obligation.
        intros x x' x_eq_x' s s' (index_eq_index' & positions_eq_positions').
        now rewrite 2!State.Ok.Raw;
        setoid_rewrite x_eq_x';
        setoid_rewrite index_eq_index';
        setoid_rewrite positions_eq_positions'.
      Qed.

      #[local]
      Existing Instance Setoid.Option_Setoid.
      #[local]
      Instance Theory :
        Algebraic.Theory Label.Signature State.Signature.
      Proof.
        split.
          apply State.Ok.initial_state.
        intros [k₀| p₀] x₀ s _ Ok_x₀_s.
          exists (State.talon s); split; [reflexivity|].
          now apply State.Ok.talon.
        simpl; destruct (Map.find p₀ s.(State.owner_to_indices))
          as [indices|] eqn: find_p₀_s.
          exists (State.assigned_mapsto s p₀ indices); split; [reflexivity|].
          now apply State.Ok.assigned_mapsto; [apply Map_Facts.find_mapsto_iff|].
        exists (State.assigned_not_in s p₀); split; [reflexivity|].
        now apply State.Ok.assigned_not_in; [apply Map_Facts.not_find_in_iff|].
      Qed.
    End State.

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

    Lemma try_fold_eq_generate_body :
      forall
      (x : list Card.t)
      (s : State.t),
      Setoid.try_fold s (Algebraic.f State.Signature) x =
      Some (generate_body x s).
    Proof.
      induction x as [| u₀ x₀ IHx₀].
        reflexivity.
      intros s; simpl; now rewrite IHx₀.
    Qed.

    Definition generate
      (cards : list Card.t) :
      Map.t (list nat) :=
      (generate_body cards State.initial_state).(State.owner_to_indices).

    #[local]
    Existing Instances
      Label.Theory
      State.Theory.
    #[local]
    Existing Instances
      Algebraic.to_Relational_Theory
      Algebraic.to_Relational_Path_Theory.
    Lemma generate_spec :
      forall
      cards : list Card.t,
      Indices.t cards (generate cards).
    Proof.
      intros cards.
      pose (Relational_Signature_L_S :=
        Algebraic.to_Relational_Signature State.Signature).
      pose (Relational_Path_Signature_L_S :=
        Algebraic.to_Relational_Path_Signature State.Signature).
      specialize (Relational.Path.executable_Initial
        (Label_Signature_L := Label.Signature)
        cards
        State.initial_state) as (t & Path_init_t & Ok_cards_t).
          constructor.
        simpl; reflexivity.
      setoid_replace (generate cards) with t.(State.owner_to_indices).
        apply Ok_cards_t.
      enough (H : Setoid.eqoptionA State.eq
        (Some (generate_body cards State.initial_state))
        (Some t)).
        inversion_clear H as [? ? H'|]; apply H'.
      now rewrite <- try_fold_eq_generate_body.
    Qed.
  End Generate.

  Module Compress.
    Module Label <:
      EqualityType.
      Definition t :
        Type :=
        Card.t.

      Definition eq :
        relation Label.t :=
        Card.eq.

      #[program]
      Instance eq_equiv :
        Equivalence Label.eq.

      #[program]
      Definition Signature
        (cards : list Card.t) :
        Label.Signature Label.eq :=
        {|
          Label.Ok x :=
            exists
            y : list Card.t,
            eqlistA Label.eq cards (y ++ x);
        |}.
      Next Obligation.
        intros x x' x_eq_x'.
        now setoid_rewrite x_eq_x'.
      Qed.

      Instance Theory
        (cards : list Card.t) :
        Label.Theory (Signature cards).
      Proof.
        constructor; intros u₀ x₀ (y & cards_eq_app_y_x).
        now exists (y ++ [u₀]); rewrite <- app_assoc.
      Qed.
    End Label.

    Module State <:
      EqualityType.
      Record State :
        Type :=
        new {
          index : nat;
          instructions : Instructions.t;
        }.

      Definition t :
        Type :=
        State.

      Definition eq :
        relation State.t :=
        fun s s' : State.t =>
          s.(State.index) = s'.(State.index) /\
          eqlistA Instruction.eq s.(State.instructions) s'.(State.instructions).

      Instance eq_equiv :
        Equivalence State.eq.
      Proof.
        split.
            intros x; split; reflexivity.
          intros x y x_eq_y; split; symmetry; apply x_eq_y.
        intros x y z x_eq_y y_eq_z; split.
            transitivity y.(State.index); [apply x_eq_y| apply y_eq_z].
        transitivity y.(State.instructions); [apply x_eq_y| apply y_eq_z].
      Qed.

      Instance Morphism_new :
        Proper (Logic.eq ==> eqlistA Instruction.eq ==> State.eq) State.new.
      Proof.
        intros
          index index' index_eq_index'
          instructions instructions' instructions_eq_instructions';
          split.
            now rewrite index_eq_index'.
        simpl; now rewrite instructions_eq_instructions'.
      Qed.

      Instance Morphism_index :
        Proper (State.eq ==> Logic.eq) State.index.
      Proof.
        intros s s' s_eq_s'.
        apply s_eq_s'.
      Qed.

      Instance Morphism_instructions :
        Proper (State.eq ==> eqlistA Instruction.eq) State.instructions.
      Proof.
        intros s s' s_eq_s'.
        apply s_eq_s'.
      Qed.

      Notation initial_state :=
        {|
          index := 0;
          instructions := [];
        |}.

      Notation nop
        s :=
        {|
          index := S s.(index);
          instructions := s.(instructions);
        |}.

      Notation assigned_both
        s
        owner :=
        {|
          index := S s.(index);
          instructions := Up owner :: Down owner :: s.(instructions);
        |}.

      Notation assigned_first
        s
        owner :=
        {|
          index := S s.(index);
          instructions := Down owner :: s.(instructions);
        |}.

      Notation assigned_last
        s
        owner :=
        {|
          index := S s.(index);
          instructions := Up owner :: s.(instructions);
        |}.

      Module Ok.
        Section Ok.
          Variables
            (cards : list Card.t)
            (owner_to_indices : Map.t (list nat))
            (Ok_indices : Indices.t cards owner_to_indices).

          Record t
            (x : list Card.t)
            (s : State.t) :
            Prop :=
            new {
              length :
                s.(State.index) = length x;
              instructions :
                Instructions.Ok s.(State.instructions);
              contains_down :
                forall
                (owner : Owner.t)
                (indices : list nat)
                (index : nat),
                Map.MapsTo owner indices owner_to_indices ->
                Last index indices ->
                In (Down owner) s.(State.instructions) <->
                s.(State.index) > index;
              contains_up :
                forall
                (owner : Owner.t)
                (indices : list nat)
                (index : nat),
                Map.MapsTo owner indices owner_to_indices ->
                Head index indices ->
                In (Up owner) s.(State.instructions) <->
                s.(State.index) > index;
            }.

          Lemma Raw :
            forall
            (x : list Card.t)
            (s : State.t),
            t x s <->
            s.(State.index) = List.length x /\
            Instructions.Ok s.(State.instructions) /\
            (forall
            (owner : Owner.t)
            (indices : list nat)
            (index : nat),
            Map.MapsTo owner indices owner_to_indices ->
            Last index indices ->
            In (Down owner) s.(State.instructions) <->
            s.(State.index) > index) /\
            (forall
            (owner : Owner.t)
            (indices : list nat)
            (index : nat),
            Map.MapsTo owner indices owner_to_indices ->
            Head index indices ->
            In (Up owner) s.(State.instructions) <->
            s.(State.index) > index).
          Proof.
            intros x s; split.
              now intros [length_x instructions_s contains_down_s contains_up_s].
            intros (length_x & instructions_s & contains_down_s & contains_up_s).
            now constructor.
          Qed.

          Lemma initial_state :
            t [] State.initial_state.
          Proof.
            constructor.
                  reflexivity.
                constructor.
            1, 2 :
              intros owner indices index _ _  ;
              rewrite InA_nil; enough (~ 0 > index); [tauto| auto with arith].
          Qed.

          Section Positions.
            Variables
              (p p' : Owner.t)
              (indices indices' : list nat)
              (MapsTo_p_indices : Map.MapsTo p indices owner_to_indices)
              (MapsTo_p'_indices' : Map.MapsTo p' indices' owner_to_indices).

            Lemma Intersecting_Positions :
              (exists
              index : nat,
              List.In index indices /\
              List.In index indices') ->
              Owner.eq p p'.
            Proof.
              intros (index & In_index_indices & In_index_indices').
              change (Card.eq (Card.Assigned p) (Card.Assigned p')).
              now apply Functional_RNthA with cards index;
              [apply Ok_indices.(positions) with indices| apply Ok_indices.(positions) with indices'].
            Qed.

            Lemma Equal_Positions :
              indices = indices' <->
              (exists
              index : nat,
              List.In index indices /\
              List.In index indices').
            Proof.
              split.
                intros <-.
                assert (InA Card.eq (Card.Assigned p) cards) as
                  (index & RNthA_p_cards_index)%RNthA_Facts.InA_iff.
                  now apply Ok_indices.(contains); exists indices.
                exists index; split; now apply Ok_indices.(positions) with p.
              intros intersecting; enough (p_eq_p' : Owner.eq p p').
                now apply Map_Facts.MapsTo_fun with owner_to_indices p;
                [| rewrite p_eq_p'].
              now apply Intersecting_Positions.
            Qed.

            Lemma Injective_Positions :
              indices = indices' ->
              Owner.eq p p'.
            Proof.
              rewrite Equal_Positions by assumption.
              now apply Intersecting_Positions.
            Qed.

            Lemma case_eq :
              forall
              index index' : nat,
              Last index indices /\ Last index' indices' \/
              Head index indices /\ Head index' indices' ->
              Owner.eq p p' <-> index = index'.
            Proof.
              intros index index' H.
              split.
                intros p_eq_p'; rewrite <- p_eq_p' in MapsTo_p'_indices'.
                enough (indices = indices') as <-.
                  destruct H as [
                    (Last_index_indices & Last_index'_indices)|
                    (Head_index_indices & Head_index'_indices)].
                    now apply Functional_Last with indices.
                  now apply Functional_Head with indices.
                now apply Map_Facts.MapsTo_fun with owner_to_indices p.
              intros <-.
              apply Intersecting_Positions; exists index.
              destruct H as [
                (Last_index_indices & Last_index_indices')|
                (Head_index_indices & Head_index_indices')];
              now split; (apply In_Last + apply In_Head).
            Qed.

            Lemma case_neq :
              forall
              index index' : nat,
              List.In index indices ->
              ~ Last index indices /\ Last index' indices' \/
              ~ Head index indices /\ Head index' indices' ->
              index <> index'.
            Proof.
              intros index index' In_index_indices
                [(not_Last_index_indices & Last_index'_indices')|
                (not_Head_index_indices & Head_index'_indices')].
                contradict not_Last_index_indices;
                destruct not_Last_index_indices.
              2:
              contradict not_Head_index_indices;
              destruct not_Head_index_indices.
              all:
                enough (indices = indices') as -> by assumption;
                apply Equal_Positions;
                now exists index; split; [| apply In_Last + apply In_Head].
            Qed.
          End Positions.

          Lemma S_n_gt_m :
            forall
            m n : nat,
            S n > m <->
            m = n \/
            n > m.
          Proof.
            intros m n; lia.
          Qed.

          Ltac Contains_Down Ok_s₁ P :=
            intros owner indices index
              MapsTo_owner_indices Last_index_indices;
            simpl; rewrite
              1 ? cons_Up_iff,
              1 ? cons_Down_iff,
              S_n_gt_m;
            let H := fresh "H" in
            enough (H : P owner index) by
              (rewrite Ok_s₁.(contains_down) with
                (1 := MapsTo_owner_indices)
                (2 := Last_index_indices);
              simpl in H;
              lia || intuition).

          Ltac Contains_Up Ok_s₁ P :=
            intros owner indices index
              MapsTo_owner_indices Head_index_indices;
            simpl; rewrite
              1 ? Instructions.Ahead.cons_Up_iff,
              1 ? Instructions.Ahead.cons_Down_iff,
              S_n_gt_m;
            let H := fresh "H" in
            enough (H : P owner index) by
              (rewrite Ok_s₁.(contains_up) with
                (1 := MapsTo_owner_indices)
                (2 := Head_index_indices);
              simpl in H;
              lia || intuition).

          Variables
            (k₀ : Key.t)
            (p₀ : Owner.t)
            (x₀ : list Card.t)
            (s₁ : State.t)
            (Ok_s₁ : t x₀ s₁).

          Lemma index₁_to_u₀ :
            forall u₀ : Card.t,
            (Label.Signature cards).(Label.Ok) (u₀ :: x₀) ->
            RNthA.t u₀ cards s₁.(State.index).
          Proof.
            intros u₀ Ok_x.
            destruct Ok_x as (y & ->).
            rewrite Ok_s₁.(length), RNthA_Facts.middle_iff.
            now destruct u₀.
          Qed.

          Lemma talon :
            (Label.Signature cards).(Label.Ok) (Card.Talon k₀ :: x₀) ->
            t (Card.Talon k₀ :: x₀) (State.nop s₁).
          Proof.
            intros Ok_x.
            specialize (index₁_to_u₀ Ok_x) as index₁_to_k₀.
            constructor.
                  apply eq_S, Ok_s₁.(length).
                apply Ok_s₁.(instructions).
              Contains_Down Ok_s₁ (fun (owner : Owner.t) (index : nat) =>
                index <> s₁.(State.index)).
            2 :
            Contains_Up Ok_s₁ (fun (owner : Owner.t) (index : nat) =>
              index <> s₁.(State.index)).
            all:
              assert (H' : ~ Card.eq (Card.Assigned owner) (Card.Talon k₀)) by
                auto;
              contradict H'; destruct H'; apply
                Functional_RNthA with (2 := index₁_to_k₀),
               Ok_indices.(positions) with (1 := MapsTo_owner_indices).
              now apply In_Last.
            now apply In_Head.
          Qed.

          Variables
            (Ok_x : (Label.Signature cards).(Label.Ok) (Card.Assigned p₀ :: x₀)).

          Lemma assigned_assumptions :
            exists indices₀ : list nat,
            Map.MapsTo p₀ indices₀ owner_to_indices /\
            List.In s₁.(State.index) indices₀.
          Proof.
            specialize (index₁_to_u₀ Ok_x) as index₁_to_p₀.
            enough (exists indices₀ : list nat,
              Map.MapsTo p₀ indices₀ owner_to_indices) as
              (indices₀ & MapsTo_p₀_indices₀).
              now exists indices₀; split;
              [| apply Ok_indices.(positions) with (1 := MapsTo_p₀_indices₀)].
            now apply Ok_indices.(contains), RNthA_Facts.InA_iff; exists s₁.(State.index).
          Qed.

          Variables
            (indices₀ : list nat)
            (MapsTo_p₀_indices₀ : Map.MapsTo p₀ indices₀ owner_to_indices)
            (In_index₁_indices₀ : List.In s₁.(State.index) indices₀).

          Lemma assigned_both :
            Last s₁.(State.index) indices₀ ->
            Head s₁.(State.index) indices₀ ->
            t (Card.Assigned p₀ :: x₀) (State.assigned_both s₁ p₀).
          Proof with auto.
            intros Last_index_indices₀ Head_index_indices₀.
            constructor.
                  apply eq_S, Ok_s₁.(length).
                enough (Instructions.Ok (Down p₀ :: s₁.(State.instructions))) by
                  now constructor; [apply Instructions.Active.cons_Down_hd|].
                constructor; [| apply Ok_s₁.(instructions)].
                rewrite Ok_s₁.(contains_down) with
                  (1 := MapsTo_p₀_indices₀)
                  (2 := Last_index_indices₀).
                lia.
              Contains_Down Ok_s₁ (fun (owner : Owner.t) (index : nat) =>
                Owner.eq owner p₀ <-> index = s₁.(State.index)).
              apply (case_eq MapsTo_owner_indices MapsTo_p₀_indices₀)...
            Contains_Up Ok_s₁ (fun (owner : Owner.t) (index : nat) =>
              Owner.eq owner p₀ <-> index = s₁.(State.index)).
            apply (case_eq MapsTo_owner_indices MapsTo_p₀_indices₀)...
          Qed.

          Lemma assigned_first :
            Last s₁.(State.index) indices₀ ->
            ~ Head s₁.(State.index) indices₀ ->
            t (Card.Assigned p₀ :: x₀) (State.assigned_first s₁ p₀).
          Proof with auto.
            intros Last_index_indices₀ not_Head_index_indices₀.
            constructor.
                  apply eq_S, Ok_s₁.(length).
                constructor; [| apply Ok_s₁.(instructions)].
                rewrite Ok_s₁.(contains_down) with
                  (1 := MapsTo_p₀_indices₀)
                  (2 := Last_index_indices₀).
                lia.
              Contains_Down Ok_s₁ (fun (owner : Owner.t) (index : nat) =>
                Owner.eq owner p₀ <-> index = s₁.(State.index)).
              apply (case_eq MapsTo_owner_indices MapsTo_p₀_indices₀)...
            Contains_Up Ok_s₁ (fun (owner : Owner.t) (index : nat) =>
              s₁.(State.index) <> index).
            apply (case_neq MapsTo_p₀_indices₀ MapsTo_owner_indices)...
          Qed.

          Lemma assigned_last :
            ~ Last s₁.(State.index) indices₀ ->
            Head s₁.(State.index) indices₀ ->
            t (Card.Assigned p₀ :: x₀) (State.assigned_last s₁ p₀).
          Proof with auto.
            intros not_Last_index_indices₀ Head_index_indices₀.
            constructor.
                  apply eq_S, Ok_s₁.(length).
                constructor; [| apply Ok_s₁.(instructions)].
                split.
                  rewrite Ok_s₁.(contains_up) with
                    (1 := MapsTo_p₀_indices₀)
                    (2 := Head_index_indices₀).
                  lia.
                assert (exists n : nat,
                  Last n indices₀ /\
                  n <> s₁.(State.index)) as
                  (n & Last_n_indices₀ & n_neq_index₁).
                  destruct indices₀ as [| v₀ y₀].
                    inversion Head_index_indices₀.
                  exists (last y₀ v₀); split; [reflexivity|].
                  contradict not_Last_index_indices₀; simpl; now f_equal.
                apply Ok_s₁.(contains_down) with
                  (1 := MapsTo_p₀_indices₀)
                  (2 := Last_n_indices₀).
                specialize Sorted_Head_Last with
                  (1 := Ok_indices.(sorted) MapsTo_p₀_indices₀)
                  (2 := Head_index_indices₀)
                  (3 := Last_n_indices₀).
                lia.
              Contains_Down Ok_s₁ (fun (owner : Owner.t) (index : nat) =>
                s₁.(State.index) <> index).
              apply (case_neq MapsTo_p₀_indices₀ MapsTo_owner_indices)...
            Contains_Up Ok_s₁ (fun (owner : Owner.t) (index : nat) =>
              Owner.eq owner p₀ <-> index = s₁.(State.index)).
            apply (case_eq MapsTo_owner_indices MapsTo_p₀_indices₀)...
          Qed.

          Lemma assigned_middle :
            ~ Last s₁.(State.index) indices₀ ->
            ~ Head s₁.(State.index) indices₀ ->
            t (Card.Assigned p₀ :: x₀) (State.nop s₁).
          Proof with auto.
            intros not_Last_index₁_indices₀ not_Head_index₁_indices₀.
            constructor.
                  apply eq_S, Ok_s₁.(length).
                apply Ok_s₁.(instructions).
              Contains_Down Ok_s₁ (fun (owner : Owner.t) (index : nat) =>
                s₁.(State.index) <> index).
              apply (case_neq MapsTo_p₀_indices₀ MapsTo_owner_indices)...
            Contains_Up Ok_s₁ (fun (owner : Owner.t) (index : nat) =>
              s₁.(State.index) <> index).
            apply (case_neq MapsTo_p₀_indices₀ MapsTo_owner_indices)...
          Qed.
        End Ok.
      End Ok.

      #[local]
      Existing Instance
        Setoid.Option_Setoid.
      #[local]
      Existing Instances
        Setoid.Morphism_Some
        Setoid.Morphism_pair
        Setoid.Morphism_cons.
      #[local]
      Existing Instances
        Setoid.Morphism_if_then_else
        Setoid.Morphism_bind_pointwise.
      Unset Program Cases.
      #[program]
      Definition Signature
        (owner_to_indices : Map.t (list nat)) :
        Algebraic.Signature Label.eq State.eq :=
        {|
        Algebraic.init :=
          State.initial_state;
        Algebraic.f s₁ u₀ :=
          match u₀ with
          | Card.Talon k₀ =>
              Some (State.nop s₁)
          | Card.Assigned p₀ =>
              bind (Map.find p₀ owner_to_indices) (fun indices =>
              bind (last_error indices) (fun last =>
              bind (hd_error indices) (fun head =>
              let index := s₁.(State.index) in
              let instructions :=
              if_then_else
                (Nat.eqb index last)
                (if_then_else
                  (Nat.eqb index head)
                  (Up p₀ :: Down p₀ :: instructions s₁)
                  (Down p₀ :: instructions s₁))
                (if_then_else
                   (Nat.eqb index head)
                   (Up p₀ :: instructions s₁)
                   (instructions s₁)) in
              Some {|
                State.index :=
                  S s₁.(State.index);
                State.instructions :=
                  instructions;
              |})))
          end;
          Algebraic.Ok :=
            State.Ok.t owner_to_indices;
      |}.
      Next Obligation.
        intros s₁ s₁' s₁_eq_s₁' u₀ u₀' u₀_eq_u₀'.
        destruct u₀ as [k₀| p₀], u₀' as [k₀'| p₀'].
              simpl.
              now rewrite s₁_eq_s₁'.
            contradiction.
          contradiction.
        change (Owner.eq p₀ p₀') in u₀_eq_u₀'.
        now setoid_rewrite u₀_eq_u₀';
        setoid_rewrite s₁_eq_s₁'.
      Qed.
      Next Obligation.
        intros x x' x_eq_x' s s' (index_eq_index' & instructions_eq_instructions').
        rewrite 2!State.Ok.Raw;
        setoid_rewrite x_eq_x'.
        setoid_rewrite index_eq_index'.
        now setoid_rewrite instructions_eq_instructions'.
      Qed.

      #[local]
      Instance Theory
        (cards : list Card.t)
        (owner_to_indices : Map.t (list nat))
        (Ok_indices : Indices.t cards owner_to_indices) :
        Algebraic.Theory
          (Label.Signature cards)
          (State.Signature owner_to_indices).
      Proof.
        split.
          apply State.Ok.initial_state.
        intros [k₀| p₀] x₀ s₁ Ok_x Ok_s₁.
          exists (State.nop s₁); split; [reflexivity|].
          now apply State.Ok.talon with (1 := Ok_indices).
        specialize (Ok.assigned_assumptions Ok_indices Ok_s₁ Ok_x) as
          (indices₀ & MapsTo_p₀_indices₀ & In_index₁_indices₀).
        simpl; specialize Map.find_1 with (1 := MapsTo_p₀_indices₀) as ->; simpl.
        assert (exists last : nat, Last last indices₀) as
          (last & Last_last_indices₀) by
          now destruct indices₀ as [| index₀ indices₀];
          [| exists (List.last indices₀ index₀)].
        assert (exists head : nat, Head head indices₀) as
          (head & Head_head_indices₀) by
          now destruct indices₀ as [| index₀ indices₀];
          [| exists index₀].
        rewrite Last_last_indices₀, Head_head_indices₀; simpl.
        assert (reflect_Last : Bool.reflect
          (Last s₁.(State.index) indices₀)
          (Nat.eqb (s₁.(State.index)) last)).
          destruct (Nat.eqb (s₁.(State.index)) last) eqn: eqb_index₁_last;
          constructor.
            now apply PeanoNat.Nat.eqb_eq in eqb_index₁_last as ->.
          apply PeanoNat.Nat.eqb_neq in eqb_index₁_last;
          contradict eqb_index₁_last.
          now apply Functional_Last with indices₀.
        assert (reflect_Head : Bool.reflect
          (Head s₁.(State.index) indices₀)
          (Nat.eqb (s₁.(State.index)) head)).
          destruct (Nat.eqb (s₁.(State.index)) head) eqn: eqb_index₁_head; constructor.
            now apply PeanoNat.Nat.eqb_eq in eqb_index₁_head as ->.
          apply PeanoNat.Nat.eqb_neq in eqb_index₁_head;
          contradict eqb_index₁_head.
          now apply Functional_Head with indices₀.
        destruct
          reflect_Last as [Last_index₁_indices₀| not_Last_index₁_indices₀],
          reflect_Head as [Head_index₁_indices₀| not_Head_index₁_indices₀];
          simpl.
              exists (assigned_both s₁ p₀); split; [reflexivity|].
              now apply Ok.assigned_both with cards indices₀.
            exists (State.assigned_first s₁ p₀); split; [reflexivity|].
            now apply Ok.assigned_first with cards indices₀.
          exists (State.assigned_last s₁ p₀); split; [reflexivity|].
          now apply Ok.assigned_last with cards indices₀.
        exists (State.nop s₁); split; [reflexivity|].
        now apply Ok.assigned_middle with cards indices₀.
      Qed.
    End State.

    Definition compress
      (cards : list Card.t)
      (owner_to_indices : Map.t (list nat)) :
      option Instructions.t :=
      option_map
        State.instructions
        (Setoid.try_fold
          State.initial_state
          (Algebraic.f (State.Signature owner_to_indices))
          cards).

    #[local]
    Existing Instances
      Label.Theory
      State.Theory.
    #[local]
    Existing Instances
      Algebraic.to_Relational_Theory
      Algebraic.to_Relational_Path_Theory.
    Lemma compress_spec :
      forall
      (cards : list Card.t)
      (owner_to_indices : Map.t (list nat)),
      Indices.t cards owner_to_indices ->
      exists
      instructions : Instructions.t,
      compress cards owner_to_indices = Some instructions /\
      Instructions.Ok instructions.
    Proof.
      intros cards owner_to_indices Ok_indices.
      pose (Relational_Signature_L_S :=
        Algebraic.to_Relational_Signature (State.Signature owner_to_indices)).
      pose (Relational_Path_Signature_L_S :=
        Algebraic.to_Relational_Path_Signature (State.Signature owner_to_indices)).
      assert (Theory_L_S : Algebraic.Theory
        (Label.Signature cards)
        (State.Signature owner_to_indices)) by
        now apply State.Theory.
      specialize (Relational.Path.executable_Initial
        (Label_Signature_L := Label.Signature cards)
        cards
        State.initial_state) as (t & Path_init_t & Ok_cards_t).
          now exists [].
        simpl; reflexivity.
      change (Setoid.eqoptionA State.eq (
        Setoid.try_fold
        State.initial_state
        (Algebraic.f (State.Signature owner_to_indices))
        cards) (Some t)) in Path_init_t;
      unfold compress;
      destruct (Setoid.try_fold
        State.initial_state
        (Algebraic.f (State.Signature owner_to_indices))
        cards) as [t'|];
        inversion_clear Path_init_t as [? ? t'_eq_t|].
      exists t'.(State.instructions); split; [reflexivity|].
      rewrite t'_eq_t; apply Ok_cards_t.
    Qed.
  End Compress.
End Make.

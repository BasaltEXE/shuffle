Set Implicit Arguments.
Set Printing Projections.

Require Import Coq.Structures.Equalities Coq.Structures.EqualitiesFacts.
Require Import Coq.Structures.Orders Coq.Structures.OrdersFacts.

Require Import Coq.Lists.SetoidList.
Import ListNotations.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Classes.RelationClasses.

Require Import Coq.Arith.Arith.

Require Coq.MSets.MSets.
Require Coq.FSets.FMaps.

Require Import Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Require Import Setoid.

Require Import Shuffle.Misc.
Require Import Shuffle.List.
Require Shuffle.Assigned.Instructions.
Require Import Shuffle.Coloring.

Module WFacts_fun' (Key : DecidableTypeOrig) (Map : FMapInterface.WSfun Key).
  Include FMapFacts.WFacts_fun Key Map. (* TODO *)

  Lemma find_spec : forall
    [elt : Type]
    (m : Map.t elt)
    (x : Map.key),
    OptionSpec
      (fun e : elt => Map.MapsTo x e m)
      (~ Map.In x m)
      (Map.find x m).
  Proof.
    intros elt m x.
    destruct (Map.find x m) eqn: find; constructor.
      now apply find_mapsto_iff.
    now apply not_find_in_iff.
  Qed.

  Lemma find_In_Some : forall
    [elt : Type]
    (m : Map.t elt)
    (x : Map.key),
    Map.In x m ->
    exists e : elt,
      Map.find x m = Some e /\
      Map.MapsTo x e m.
  Proof.
    intros elt m x m_in_x.
    destruct (Map.find x m) as [e|] eqn: find.
      exists e.
      now split; [| apply find_mapsto_iff].
    now contradict find; apply in_find_iff.
  Qed.

  Lemma add_eq_mapsto_iff : forall
    [elt : Type]
    (m : Map.t elt)
    (x y : Map.key)
    (e e' : elt),
    Key.eq x y ->
      Map.MapsTo y e' (Map.add x e m) <->
      e = e'.
  Proof.
    intros; rewrite add_mapsto_iff; tauto.
  Qed.

  Lemma add_not_in_iff : forall
    [elt : Type]
    (m : Map.t elt)
    (x y : Map.key)
    (e : elt),
    ~ Map.In y (Map.add x e m) <->
      ~ Key.eq x y /\
      ~ Map.In y m.
  Proof.
    intros elt m x y e.
    rewrite add_in_iff; tauto.
  Qed.

  Lemma add_not_in : forall
    [elt : Type]
    (m : Map.t elt)
    (x y : Map.key)
    (e : elt),
    ~ Key.eq x y ->
    ~ Map.In y m ->
    ~ Map.In y (Map.add x e m).
  Proof.
    intros elt m x y e.
    rewrite add_in_iff; tauto.
  Qed.
End WFacts_fun'.

Module Make (Owner : DecidableTypeBoth) (Map : FMapInterface.WSfun Owner).
  Module Coloring := Coloring.Make Owner Map.

  Module Import Instructions := Instructions.Make Owner.
  Import Instructions.Notations.

  Module Import Facts := WFacts_fun' Owner Map.

  Ltac split_left :=
    split; [| try split_left].
  Ltac my_auto :=
    auto with relations instructions.

  Import Instructions.Ok.
  Import Instructions.Hints.

  Definition Synced
    (instructions : list Instruction.t)
    (coloring : Coloring.t) :
    Prop := forall
      owner : Owner.t,
      (Active owner instructions ->
      Coloring.Contains coloring owner) /\
      (Ahead owner instructions ->
      ~ Coloring.Contains coloring owner).

  Module Regular.
    Definition Color_Ok
      (instructions : list Instruction.t)
      (coloring : Coloring.t)
      (color : nat) :
      Prop :=
      (forall
        (owner : Owner.t)
        (n : nat),
        Active owner instructions ->
        Coloring.MapsTo coloring owner n ->
        color <> n) /\
      (exists
        owner : Owner.t,
        Coloring.MapsTo coloring owner color /\
        Absent owner instructions).

    Fixpoint regular_body
      (instructions : list Instruction.t)
      (coloring : Coloring.t)
      (unused_colors : list nat) :
      option Coloring.t :=
      match instructions, unused_colors with
      | Up owner :: tail, [] =>
        regular_body
          tail
          (Coloring.add_eq coloring owner)
          []
      | Up owner :: tail, color :: unused_colors =>
        regular_body
          tail
          (Coloring.add_lt coloring owner color)
          unused_colors
      | Down owner :: tail, unused_colors =>
          bind(Coloring.find coloring owner) (fun color =>
          regular_body
            tail
            coloring
            (color :: unused_colors))
      | [], _ => ret coloring
      end.

    Definition regular
      (instructions : list Instruction.t) :
      option Coloring.t :=
      regular_body
        instructions
        Coloring.empty
        [].

    Module Type AssumptionType.
      Parameter Ok : list Instruction.t -> Coloring.t -> list nat -> Prop.

      Section Properties.
        Variable p₀ : Owner.t.
        Variable x₀ : list Instruction.t.
        Variable coloring : Coloring.t.
        Variable color : nat.
        Variable unused_colors : list nat.
        Variable result : option Coloring.t.

        Parameter cons_Up_eq :
          Ok (Up p₀ :: x₀) coloring [] ->
          Ok x₀ (Coloring.add_eq coloring p₀) [].

        Parameter cons_Up_lt :
          Ok (Up p₀ :: x₀) coloring (color :: unused_colors) ->
          Ok x₀ (Coloring.add_lt coloring p₀ color) unused_colors.

        Parameter cons_Down :
          Ok (Down p₀ :: x₀) coloring unused_colors ->
          exists color : nat,
            Coloring.MapsTo coloring p₀ color /\
            Ok x₀ coloring (color :: unused_colors).
      End Properties.
    End AssumptionType.

    Definition RealColoring
      (coloring : Coloring.t)
      (instructions : list Instruction.t) :
      Prop :=
      forall owner owner' : Owner.t,
        ~ Owner.eq owner owner' ->
        Active owner instructions ->
        Active owner' instructions ->
        forall color color' : nat,
          Coloring.MapsTo coloring owner color ->
          Coloring.MapsTo coloring owner' color' ->
          color <> color'.

    Ltac Ok_destruct ok :=
      destruct ok as
        (Ok_instructions &
        Ok_coloring &
        Synced_coloring &
        Proper_coloring &
        Ok_unused_colors &
        NoDup_unused_colors).

    Module Assumption <: AssumptionType.
      Definition Ok
        (instructions : list Instruction.t)
        (coloring : Coloring.t)
        (unused_colors : list nat) :
        Prop :=
        Instructions.Ok instructions /\
        Coloring.Ok coloring /\
        Synced instructions coloring /\
        RealColoring coloring instructions /\
        Forall (Color_Ok instructions coloring) unused_colors /\
        NoDup unused_colors.

      Section Properties.
        Variable p₀ : Owner.t.
        Variable x₀ : list Instruction.t.
        Variable coloring : Coloring.t.
        Variable color : nat.
        Variable unused_colors : list nat.

        Lemma cons_Up_eq :
          Ok (Up p₀ :: x₀) coloring [] ->
          Ok x₀ (Coloring.add_eq coloring p₀) [].
        Proof with my_auto.
          intros ok; Ok_destruct ok.
          assert (not_In_p₀ : ~ Coloring.Contains coloring p₀).
            apply Synced_coloring...
          unfold Ok.
          split_left...
                now apply Instructions.Ok.cons_inv in Ok_instructions.
              apply Coloring.Ok.add_eq, Synced_coloring...
            intros p.
            split.
              intros Active_p.
              apply add_in_iff.
              destruct (Owner.eq_dec p₀ p) as [eq| neq];
                [left| right; apply Synced_coloring]...
            intros Ahead_p₀.
            apply add_not_in, Synced_coloring...
            enough (Active p₀ x₀)...
          intros x y x_neq_y Active_x Active_y m n.
          simpl; rewrite ?add_mapsto_iff.
          intros
            [(p₀_eq_x & <-)| (p₀_neq_x & x_to_m)]
            [(p₀_eq_y & <-)| (p₀_neq_y & y_to_m)].
                now contradict x_neq_y; transitivity p₀.
              enough (n <> coloring.(Coloring.colors)) by firstorder.
              now apply Nat.lt_neq, Ok_coloring; exists y.
            now apply Nat.lt_neq, Ok_coloring; exists x.
          apply Proper_coloring with x y...
        Qed.

        Lemma cons_Up_lt :
          Ok (Up p₀ :: x₀) coloring (color :: unused_colors) ->
          Ok x₀ (Coloring.add_lt coloring p₀ color) unused_colors.
        Proof with my_auto.
          intros ok; Ok_destruct ok.
          apply Forall_cons_iff in Ok_unused_colors as (Ok_color & Ok_unused_colors).
          apply NoDup_cons_iff in NoDup_unused_colors as (not_In_color & NoDup_unused_colors).
          assert (not_In_p₀ : ~ Coloring.Contains coloring p₀).
            apply Synced_coloring...
          split_left...
                  now apply Instructions.Ok.cons_inv with (Up p₀).
                apply Coloring.Ok.add_lt, Ok_coloring...
                destruct Ok_color as (_ & p & p_to_color & _).
                now exists p.
              intros p.
              split.
                intros Active_p.
                apply add_in_iff.
                destruct (Owner.eq_dec p₀ p) as [eq| neq];
                  [left| right; apply Synced_coloring]...
              intros Ahead_p₀.
              apply add_not_in, Synced_coloring; enough (Active p₀ x₀)...
            intros x y x_neq_y Active_x Active_y m n.
            simpl; rewrite ?add_mapsto_iff.
            intros
              [(p₀_eq_x & <-)| (p₀_neq_x & x_to_m)]
              [(p₀_eq_y & <-)| (p₀_neq_y & y_to_m)].
                  now contradict x_neq_y; transitivity p₀.
                apply Ok_color with y...
                enough (color <> m) by firstorder.
              apply Ok_color with x...
            apply Proper_coloring with x y...
          eapply Forall_impl, Forall_and with (1 := Ok_unused_colors), not_In_Forall, not_In_color.
          intros n ((Proper_n & Synced_n) & color_neq_n).
          split.
            intros p n' Active_p.
            simpl; rewrite add_mapsto_iff.
            intros [(p₀_eq_p & <-)| (p₀_neq_p & p_to_n)].
              auto with arith.
            apply Proper_n with p...
          destruct Synced_n as (p & p_to_n & not_In_Down_p).
          assert (p₀_neq_p: ~ Owner.eq p₀ p).
            contradict not_In_Down_p; rewrite <- not_In_Down_p.
            apply Instructions.Orthogonal.Up_impl_Down...
          exists p; split...
          apply Map.add_2...
        Qed.

        Lemma cons_Down :
          Ok (Down p₀ :: x₀) coloring unused_colors ->
          exists color : nat,
            Coloring.MapsTo coloring p₀ color /\
            Ok x₀ coloring (color :: unused_colors).
        Proof with my_auto.
          clear color; intros (Ok_x₀ & Ok_coloring & Synced_coloring & Real & Ok_unused_colors & NoDup_unused_colors).
          assert (In_p₀ : Coloring.Contains coloring p₀).
            apply Synced_coloring...
          specialize find_In_Some with (1 := In_p₀) as
            (color & _ & p₀_to_color);
            exists color.
          split_left...
                  now apply Instructions.Ok.cons_inv in Ok_x₀.
                intros p.
                split.
                  intros Active_p.
                  apply Synced_coloring...
                intros Ahead_p.
                apply Synced_coloring...
              intros x y x_neq_y Active_x Active_y m n x_to_m y_to_n.
              apply Real with x y...
            constructor.
              split.
                intros p color' Active_p p_to_color'.
                apply Real with p₀ p...
                enough (Absent p₀ x₀)...
              exists p₀...
            eapply Forall_impl with (2 := Ok_unused_colors).
            intros n (H & p & p_to_color & not_InDown_p).
            split.
              intros x m Active_x x_to_m.
              apply H with x...
            exists p...
          constructor...
          apply not_In_Forall, Forall_impl with (2 := Ok_unused_colors).
          intros n [Proper_n Synced_n].
          enough (n <> color) by auto with arith.
          apply Proper_n with p₀...
        Qed.
      End Properties.
    End Assumption.

    Module Type Proposition.
      Parameter t :
        Instructions.t ->
        Coloring.t ->
        list nat ->
        option Coloring.t ->
        Prop.
    End Proposition.

    Module Type BaseCase (P : Proposition).
      Section Basis.
        Variables
          (coloring : Coloring.t)
          (unused_colors : list nat).

        Parameter nil :
          Assumption.Ok [] coloring unused_colors ->
          P.t [] coloring unused_colors (Some coloring).
      End Basis.
    End BaseCase.

    Module Type InductionSteps (P : Proposition).
      Section Steps.
        Variables
          (p₀ : Owner.t)
          (x₀ : Instructions.t)
          (coloring : Coloring.t)
          (color : nat)
          (unused_colors : list nat)
          (result : option Coloring.t).

        Parameter cons_Up_eq :
          Assumption.Ok (Up p₀ :: x₀) coloring [] ->
          P.t x₀ (Coloring.add_eq coloring p₀) [] result ->
          P.t (Up p₀ :: x₀) coloring [] result.

        Parameter cons_Up_lt :
          Assumption.Ok (Up p₀ :: x₀) coloring (color :: unused_colors) ->
          P.t x₀ (Coloring.add_lt coloring p₀ color) unused_colors result ->
          P.t (Up p₀ :: x₀) coloring (color :: unused_colors) result.

        Parameter cons_Down :
          Coloring.MapsTo coloring p₀ color ->
          Assumption.Ok (Down p₀ :: x₀) coloring unused_colors ->
          P.t x₀ coloring (color :: unused_colors) result ->
          P.t (Down p₀ :: x₀) coloring unused_colors result.
      End Steps.
    End InductionSteps.

    Module InductionPrinciple (P : Proposition) (B : BaseCase P) (S : InductionSteps P).
      Lemma ind :
        forall
          (instructions : Instructions.t)
          (coloring : Coloring.t)
          (unused_colors : list nat),
          Assumption.Ok
            instructions
            coloring
            unused_colors ->
          P.t
            instructions
            coloring
            unused_colors
            (regular_body instructions coloring unused_colors).
      Proof.
        induction instructions as [| ([|] & p₀) x₀ IHx₀];
          intros coloring unused_colors ok.
            now apply B.nil.
          destruct unused_colors as [| color unused_colors].
            now apply S.cons_Up_eq, IHx₀, Assumption.cons_Up_eq.
          now apply S.cons_Up_lt, IHx₀, Assumption.cons_Up_lt.
        specialize Assumption.cons_Down with (1 := ok) as
          (color & p₀_to_color & ok').
        simpl; rewrite Map.find_1 with (1 := p₀_to_color); simpl.
        now apply S.cons_Down with color, IHx₀.
      Qed.
    End InductionPrinciple.

    Definition Synced'
      (instructions : list Instruction.t)
      (coloring result : Coloring.t) :=
      (forall (owner : Owner.t) (color : nat),
      ~ Ahead owner instructions ->
      Coloring.MapsTo result owner color ->
      Coloring.MapsTo coloring owner color).

    Lemma regular_body_spec : forall
      (instructions : list Instruction.t)
      (coloring : Coloring.t)
      (unused_colors : list nat),
      Assumption.Ok instructions coloring unused_colors ->
      OptionSpec (fun result : Coloring.t =>
        Coloring.Ok result /\
        Skip.Forall (RealColoring result) instructions /\
        Synced' instructions coloring result)
        False
        (regular_body instructions coloring unused_colors).
    Proof with my_auto.
      induction instructions as [| [[|] owner] instructions IHinstructions];
        intros coloring unused_colors ok.
            Ok_destruct ok.
          constructor; split_left...
          apply Skip.Forall.nil.
            intros x y x_neq_y Active_x Active_y.
            absurd (Active x [])...
          intros owner' color' not_Ahead_owner' owner'_to_color'...
        destruct unused_colors as [| color unused_colors].
          pose proof (ok' := Assumption.cons_Up_eq ok).
          specialize IHinstructions with (1 := ok').
          apply OptionSpec_impl with (2 := IHinstructions).
          intros result (Ok_result & Proper_result & Synced_result).
          Ok_destruct ok'.
          split_left...
            apply Skip.Forall.cons...
            intros x y x_neq_y Active_x Active_y m n x_to_m y_to_n.
            apply Proper_coloring with x y...
            1 - 2:
              now apply Instructions.Active.cons_Up_inv with owner.
            1 - 2:
            destruct
              Active_x as (not_Ahead_x & _),
              Active_y as (not_Ahead_y & _);
            apply Synced_result...
          intros owner' color' not_Ahead_owner' owner'_to_color'.
          rewrite Instructions.Ahead.cons_Up_iff in not_Ahead_owner'.
          apply Map.add_3 with owner coloring.(Coloring.colors),
            Synced_result...
        pose proof (ok' := Assumption.cons_Up_lt ok).
        specialize IHinstructions with (1 := ok').
        apply OptionSpec_impl with (2 := IHinstructions).
        intros result (Ok_result & Proper_result & Synced_result).
        Ok_destruct ok'.
        split_left...
          apply Skip.Forall.cons...
          intros x y x_neq_y Active_x Active_y m n x_to_m y_to_n.
          apply Proper_coloring with x y...
          1 - 2:
            now apply Instructions.Active.cons_Up_inv with owner.
          1 - 2:
          destruct
            Active_x as (not_Ahead_x & _),
            Active_y as (not_Ahead_y & _);
          apply Synced_result...
        intros owner' color' not_Ahead_owner' owner'_to_color'.
        rewrite Instructions.Ahead.cons_Up_iff in not_Ahead_owner'.
        apply Map.add_3 with owner color,
          Synced_result...
      simpl in *.
      specialize Assumption.cons_Down with (1 := ok) as
        (color & owner_to_color & ok').
      rewrite Map.find_1 with (1 := owner_to_color).
      specialize IHinstructions with (1 := ok').
      apply OptionSpec_impl with (2 := IHinstructions).
      intros result (Ok_result & Proper_result & Synced_result).
      split_left...
        apply Skip.Forall.cons...
        intros x y x_neq_y Active_x Active_y m n x_to_m y_to_n.
        assert (Ok_instructions' : Instructions.Ok (Down owner :: instructions)) by
          now destruct ok.
        Ok_destruct ok.
        apply Proper_coloring with x y...
        1 - 2:
        destruct
          Active_x as (not_Ahead_x & _),
          Active_y as (not_Ahead_y & _);
        apply Synced_result...
      intros owner' color' not_Ahead_owner' owner'_to_color'.
      rewrite Instructions.Ahead.cons_Down_iff in not_Ahead_owner'.
      now apply Synced_result.
    Qed.

    Lemma regular_spec : forall
      (instructions : list Instruction.t),
      Instructions.Ok instructions ->
      Instructions.Closed instructions ->
      OptionSpec (fun result =>
        Coloring.Ok result /\
        Skip.Forall (RealColoring result) instructions)
        False
        (regular instructions).
    Proof with my_auto.
      intros instructions Ok_instructions Down_impl_Up.
      eapply OptionSpec_impl, regular_body_spec.
        intros result (Ok_result & Proper_result & _)...
      split_left...
            apply Coloring.Ok.empty.
          intros owner; split.
            intros (not_Ahead_owner & In_Down_owner).
            absurd (Ahead owner instructions)...
          intros Ahead_owner In_owner.
          apply empty_in_iff with (1 := In_owner).
        intros x y x_neq_y Active_x Active_y m n x_to_m y_to_n.
        exfalso; apply empty_mapsto_iff with (1 := x_to_m).
      constructor.
    Qed.
  End Regular.

  Module Pred.
    Definition pred_error
      (n : nat) :
      option nat :=
      match n with
      | O => None
      | S n' => Some n'
      end.

    Notation Pred n m :=
      (pred_error n = Some m).

    Notation Ok n m :=
      (n = S m)
      (only parsing).

    Section Properties.
      Variables
        (m n : nat).

      Lemma None_iff :
        pred_error n = None <->
        n = 0.
      Proof.
        now destruct n as [| n'].
      Qed.

      Lemma eq_None :
        n = 0 ->
        pred_error n = None.
      Proof.
        apply None_iff.
      Qed.

      Lemma None_eq :
        pred_error n = None ->
        n = 0.
      Proof.
        apply None_iff.
      Qed.

      Lemma Some_iff :
        Pred n m <->
        Ok n m.
      Proof.
        now destruct n as [| n'];
          [| split; intros [= ->]].
      Qed.

      Lemma Some_neq :
        Pred n m ->
        Ok n m.
      Proof.
        apply Some_iff.
      Qed.

      Lemma neq_Some :
        n <> 0 ->
        exists m : nat,
          Pred n m /\
          Ok n m.
      Proof.
        now destruct n as [| n'];
          [| exists n'].
      Qed.
    End Properties.

    Lemma pred_error_spec :
      forall n : nat,
        OptionSpec
          (fun m : nat => Ok n m)
          (n = 0)
          (pred_error n).
    Proof.
      intros n.
      now destruct n as [| n'] eqn: Pred;
        constructor.
    Qed.
  End Pred.
  Import Pred(pred_error, pred_error_spec, Pred).

  Module Active (M : MSetInterface.WSetsOn Owner).
    Module M_Facts := MSetFacts.WFactsOn Owner M.
    Module M_Properties := MSetProperties.WPropertiesOn Owner M.

    Notation Ok x s :=
      (forall
        p : Owner.t,
        M.In p s <-> Active p x).

    Fixpoint active
      (x : Instructions.t) :
      M.t :=
      match x with
      | [] =>
        M.empty
      | Up p₀ :: x₀ =>
        M.remove p₀ (active x₀)
      | Down p₀ :: x₀ =>
        M.add p₀ (active x₀)
      end.

    Notation count x :=
      (M.cardinal (active x)).

    Section Active.
      Variables
        x : Instructions.t.

      Lemma active_spec :
        Instructions.Ok x ->
        Ok x (active x).
      Proof.
        induction 1 as [| u₀ x₀ Active_u₀_x₀ Ok_x₀ IHx₀|
        u₀ x₀ Absent_u₀_x₀ Ok_x₀ IHx₀]; intros p.
            now rewrite M_Facts.empty_iff.
          simpl; rewrite M.remove_spec, Instructions.Active.cons_Up_iff, IHx₀.
          now enough (Owner.eq p u₀ <-> Owner.eq u₀ p) as ->.
        simpl; rewrite M.add_spec, Instructions.Active.cons_Down_iff, IHx₀ by
          now constructor.
        now enough (Owner.eq p u₀ <-> Owner.eq u₀ p) as ->.
      Qed.

      Lemma active_closed :
        Instructions.Ok x ->
        Instructions.Closed x ->
        M.Empty (active x).
      Proof.
        intros Ok_x Closed_x p.
        rewrite active_spec by assumption.
        now apply Instructions.Closed_not_Active.
      Qed.

      Lemma count_closed :
        Instructions.Ok x ->
        Instructions.Closed x ->
        count x = O.
      Proof.
        intros Ok_x Closed_x.
        now apply M_Properties.cardinal_Empty, active_closed.
      Qed.
    End Active.

    Section Count.
      Variables
        (p₀ : Owner.t)
        (x₀ : Instructions.t).

      Lemma count_Up :
        Instructions.Ok (Up p₀ :: x₀) ->
        S (count (Up p₀ :: x₀)) = count x₀.
      Proof.
        intros Ok_x.
        apply Instructions.Ok.cons_Up_iff in Ok_x
          as (Active_p₀ & Ok_x₀).
        now apply M_Properties.remove_cardinal_1, active_spec.
      Qed.

      Lemma count_Down :
        Instructions.Ok (Down p₀ :: x₀) ->
        count (Down p₀ :: x₀) = S (count x₀).
      Proof with my_auto.
        intros Ok_x.
        apply Instructions.Ok.cons_Down_iff in Ok_x
          as (Absent_p₀ & Ok_x₀).
        apply M_Properties.add_cardinal_2.
        rewrite active_spec by assumption.
        assert (p₀_eq_p₀ : Owner.eq p₀ p₀) by reflexivity.
        contradict p₀_eq_p₀...
      Qed.
    End Count.
  End Active.

  Module Counter.
    Module Opcode := Instructions.Opcode.

    Module M := MSetWeakList.Make Owner.
    Module Active := Active M.

    Fixpoint counter_body
      (x : Instructions.t)
      (active : nat)
      (colors : nat) :
      option nat :=
      match x with
      | [] =>
        Some colors
      | Up p₀ :: x₀ =>
        counter_body
          x₀
          (S active)
          (max (S active) colors)
      | Down p₀ :: x₀ =>
        bind (pred_error active) (fun active' : nat =>
          counter_body
            x₀
            active'
            colors)
      end.

    Definition counter
      (x : Instructions.t) :
      option nat :=
      counter_body x O O.

    Module State.
      Definition t :
        Type :=
        Instructions.t *
        nat *
        nat.

      Definition instructions
        (self : t) :
        Instructions.t :=
        let '(instructions, _, _) := self in
        instructions.

      Definition active
        (self : t) :
        nat :=
        let '(_, active, _) := self in
        active.

      Definition colors
        (self : t) :
        nat :=
        let '(_, _, colors) := self in
        colors.

      Definition Ok
        (state : t) :
        Prop :=
        (Instructions.Ok (instructions state) /\
        active state = Active.count (instructions state) /\
        active state <= colors state).
    End State.

    Inductive Max (active colors : nat) : nat -> Prop :=
    | Max_ge :
      active >= colors ->
      Max active colors (S active)
    | Max_lt :
      active < colors ->
      Max active colors colors.

    Lemma max_spec :
      forall
        active colors : nat,
        Max active colors (max (S active) colors).
    Proof.
      intros active colors.
      destruct (le_gt_dec colors active) as
        [active_ge_colers| active_lt_colors].
        now rewrite Nat.max_l; [constructor| apply le_S].
      now rewrite Nat.max_r; [constructor|].
    Qed.

    Inductive Counter :
      relation State.t :=
    | Counter_Up :
      forall
        (p₀ : Owner.t)
        (x₀ : Instructions.t)
        (active colors colors' : nat),
        Max active colors colors' ->
        Counter
          (x₀, S active, colors')
          (Up p₀ :: x₀, active, colors)
    | Counter_Down :
      forall
        (p₀ : Owner.t)
        (x₀ : Instructions.t)
        (active colors : nat),
        Counter
          (x₀, active, colors)
          (Down p₀ :: x₀, S active, colors).

    Add Parametric Morphism : State.instructions with signature
      Counter --> Tail (A := Instruction.t) as instructions_morphism.
    Proof.
      intros v₀ v₁ Counter_v₁_v₀.
      induction Counter_v₁_v₀ as
        [p₀ x₀ active₀ colors₀ colors₁ Ok_colors₁| p₀ x₀ active₀ colors₀];
        constructor.
    Qed.

    Add Parametric Morphism : (fun state => State.colors state) with signature
      Counter --> le as colors_morphism.
    Proof with auto with arith.
      intros v₀ v₁ Counter_v₁_v₀.
      induction Counter_v₁_v₀ as
        [p₀ x₀ active₀ colors₀ colors₁ Max_colors₁| p₀ x₀ active₀ colors₀];
        simpl;
        [destruct Max_colors₁|]...
    Qed.

    Add Parametric Morphism : State.Ok with signature
      Counter --> impl as Ok_morphism.
    Proof with auto with arith instructions.
      intros v₀ v₁
        [p₀ x₀ active₀ colors₀ colors₁ Max_colors₁| p₀ x₀ active₀ colors₀]
        (Ok_instructions₀ & Ok_active₀ & Ok_colors₀).
        apply Instructions.Ok.cons_Up_iff in Ok_instructions₀ as
          (Active_p₀_x₀ & Ok_x₀).
        split_left...
          simpl in *; rewrite <- Active.count_Up with p₀ x₀...
        destruct Max_colors₁...
      apply Instructions.Ok.cons_Down_iff in Ok_instructions₀ as
          (Absent_p₀_x₀ & Ok_x₀).
      split_left...
      simpl in *; rewrite
        <- Nat.succ_inj_wd,
        <- Active.count_Down with (p₀ := p₀)...
    Qed.

    Definition Graph :=
      clos_refl_trans_n1 _ Counter.

    Lemma counter_body_spec :
      forall
        (instructions : Instructions.t)
        (active : nat)
        (colors : nat),
        OptionSpec
          (fun colors' : nat =>
            exists
              active' : nat ,
              Graph
                ([], active', colors')
                (instructions, active, colors))
          (exists
            (p₀' : Owner.t)
            (x₀' : Instructions.t)
            (colors' : nat),
            Graph
              (Down p₀' :: x₀', O, colors')
              (instructions, active, colors))
          (counter_body instructions active colors).
    Proof.
      induction instructions as [| [[|] p₀] x₀ IHx₀]; intros active colors.
          constructor; exists active; constructor.
        specialize IHx₀ with (S active) (max (S active) colors).
        specialize max_spec with active colors as Max_active_colors.
        assert (H : Counter (x₀, S active, Init.Nat.max (S active) colors) (Up p₀ :: x₀, active, colors)) by
          now constructor.
        apply OptionSpec_map with (3 := IHx₀).
          intros colors' (active' & graph).
          now exists active';
            constructor 2 with (x₀, S active, Init.Nat.max (S active) colors).
        intros (p₀' & x₀' & colors' & graph).
        now exists p₀', x₀', colors';
          constructor 2 with (x₀, S active, max (S active) colors).
      simpl.
      destruct active as [| pred_active].
        constructor.
        exists p₀, x₀, colors; constructor.
      specialize IHx₀ with pred_active colors.
      assert (H : Counter (x₀, pred_active, colors) (Down p₀ :: x₀, S pred_active, colors)) by
        now constructor.
      apply OptionSpec_map with (3 := IHx₀).
        intros colors' (active' & graph).
        now exists active';
          constructor 2 with (x₀, pred_active, colors).
      intros (p₀' & x₀' & colors' & graph).
      now exists p₀', x₀', colors';
        constructor 2 with (x₀, pred_active, colors).
    Qed.

    Lemma Graph_invariant :
      forall
        state' state : State.t,
        Graph state' state ->
        State.Ok state ->
          State.Ok state' /\
          (State.instructions state' = [] ->
          (State.colors state <= State.colors state' /\
          Skip.Forall
            (fun instructions : Instructions.t =>
            Active.count instructions <= State.colors state')
            (State.instructions state)) /\
          (State.colors state' = State.colors state \/
          Skip.Exists
            (fun instructions : Instructions.t =>
            Active.count instructions = State.colors state')
            (State.instructions state))).
    Proof with auto with arith.
      intros u v.
      induction 1 as [| v₁ v₀ Counter_v₁_v₀ R_u_v₁ IHv₁];
        intros Ok_v₀.
        split; [| intros ->]...
        split;
          [split; [| apply Skip.Forall.nil]| left]...
      assert (Ok_v₁ : State.Ok v₁) by
        now rewrite Counter_v₁_v₀.
      split; [apply IHv₁| intros instructions'_eq_nil]...
      specialize IHv₁ with (1 := Ok_v₁) as (_ & IHv₁);
        specialize IHv₁ with (1 := instructions'_eq_nil)
        as ((colors_v₁_le_u & active_v₁_le_u) & IHv₁).
      destruct
        Ok_v₀ as (Ok_instructions₀ & Ok_active₀ & Ok_colors₀),
        Ok_v₁ as (Ok_instructions₁ & Ok_active₁ & Ok_colors₁).
      split.
        split.
          now rewrite <- Counter_v₁_v₀.
        intros instructions.
        assert (
          exists w z,
            State.instructions v₀ = w :: z /\
            State.instructions v₁ = z)
          as (w & z & H₀ & H₁).
          enough (Tail (State.instructions v₀) (State.instructions v₁))
            as (w & z)
            by now exists w, z.
          now apply instructions_morphism.
        rewrite H₀, H₁ in *; intros Skip_v₀_instructions.
        apply Skip.cons_iff in Skip_v₀_instructions as [->| Suffix_tail].
          rewrite <- Ok_active₀.
          transitivity (State.colors v₀); [assumption|].
          now transitivity (State.colors v₁);
            [rewrite Counter_v₁_v₀|].
        now apply active_v₁_le_u.
      destruct IHv₁ as
        [u_eq_v₁| (instructions & Skip_instructions_v₁ & u_eq_instructions)];
        [| right].
        enough (State.colors v₁ = State.colors v₀ \/ State.colors v₁ = State.active v₁)
          as [<-| H];
          [left| right|]...
          now exists (State.instructions v₁); split;
            [rewrite Counter_v₁_v₀| rewrite H, Ok_active₁ in u_eq_v₁].
        destruct Counter_v₁_v₀ as
          [p₀ x₀ active₀ colors₀ colors₁ Max_colors₁| p₀ x₀ active₀ colors₀];
          simpl in *;
          [destruct Max_colors₁|]...
      now exists instructions; split;
        [rewrite <- Counter_v₁_v₀|].
    Qed.

    Lemma counter_spec :
      forall
        instructions : Instructions.t,
        Instructions.Ok instructions ->
        Instructions.Closed instructions ->
        OptionSpec
          (fun colors' : nat =>
            Skip.Forall
              (fun instructions' : Instructions.t =>
              Active.count instructions' <= colors')
              instructions /\
            Skip.Exists
              (fun instructions' : Instructions.t =>
              Active.count instructions' = colors')
              instructions)
          False
          (counter instructions).
    Proof with auto with arith.
      intros x Ok_x Closed_x.
      assert (Ok_state : State.Ok (x, 0, 0)).
        split_left;
          [| symmetry; apply Active.count_closed|]...
      specialize counter_body_spec with x 0 0 as spec.
      apply OptionSpec_map with (3 := spec).
        intros colors' (active' & graph).
        specialize Graph_invariant with (1 := graph) (2 := Ok_state) as
          (_ & H).
        specialize H with (1 := eq_refl) as (H_Forall & H_Exists).
        split; [apply H_Forall|].
        destruct H_Exists as
          [H_Exists| H_Exists];
          simpl in *...
        exists x; split; [reflexivity| rewrite Active.count_closed]...
      intros (p₀ & x₀ & colors & graph).
      absurd (State.Ok (Down p₀ :: x₀, 0, colors)).
        intros (Ok_instructions' & Ok_active' & _);
          contradict Ok_active'.
        change (O <> Active.count (Down p₀ :: x₀)).
        rewrite Active.count_Down with p₀ x₀...
      apply Graph_invariant with (1 := graph) (2 := Ok_state).
    Qed.
  End Counter.

  Module Fixed.
    Module Type Ord.
      Include EqLtLe'.
      Include HasBoolOrdFuns'.
      Include HasCmp.
      Include CompareBasedOrder.
      Include BoolOrdSpecs.

      Include IsStrOrder.
    End Ord.

    Module Ord_to_OTF (O : Ord) <: OrderedTypeFull'.
      Include O.
      Include CompareBasedOrderFacts.
      Include HasEqBool2Dec.

      Lemma le_lteq : forall x y : t, x <= y <-> x < y \/ x == y.
      Proof.
        intros x y.
        rewrite <- compare_eq_iff, <- compare_lt_iff, <- compare_le_iff.
        destruct (compare_spec x y) as [x_eq_y| x_lt_y| x_le_y].
            now split; [right|].
          now split; [left|].
        split; [contradiction| intros [H| H]; discriminate H].
      Qed.
    End Ord_to_OTF.

    Module OrdFacts (Import O : Ord).
      Module Export OTF := Ord_to_OTF O.
      Module Export OTF_Facts := OrderedTypeFullFacts OTF.
      Module Export Facts.
        Include BoolOrderFacts O O O O O.
      End Facts.
    End OrdFacts.

    Module Min (Import O : Ord).
      Module Import Facts := OrdFacts O.
      Module Import OTF := Ord_to_OTF O.

      Definition Min
        (x : list t)
        (n : nat)
        (v : t) :
        Prop :=
        ForNth (fun (m : nat) (w : t) =>
          ((m < n)%nat -> v < w) /\
          ((m > n)%nat -> v <= w)) x /\
        Nth x n v.

      Lemma Min_fun : forall x m v n w,
        Min x m v ->
        Min x n w ->
        m = n /\ v = w.
      Proof.
        intros x m v n w (Min_m_v & m_to_v) (Min_n_w & n_to_w).
        unfold ForNth in *.
        specialize Min_m_v with (1 := n_to_w).
        specialize Min_n_w with (1 := m_to_v).
        destruct (lt_eq_lt_dec m n) as
          [[m_lt_n| ->]| m_gt_n].
            enough (w < w) by order.
            enough (w < v /\ v <= w) as (w_lt_v & v_le_w) by order.
            now split; [apply Min_n_w| apply Min_m_v].
          enough (Some v = Some w) as [= v_eq_w] by easy.
          now transitivity (nth_error x n).
        enough (v < v) by order.
        enough (v < w /\ w <= v) as (v_lt_w & w_le_v) by order.
        now split; [apply Min_m_v| apply Min_n_w].
      Qed.

      Section Properties.
        Variables
          (u₀ : t)
          (x₀ : list t)
          (n : nat)
          (v : t).

        Lemma nil_inv :
          ~ Min [] n v.
        Proof.
          intros (_ & n_to_v).
          now apply Nth.nil_inv in n_to_v.
        Qed.

        Lemma nil_iff :
          Min [] n v <-> False.
        Proof.
          split;
            [apply nil_inv| easy].
        Qed.

        Lemma cons_le :
          ForNth (fun n u => u₀ <= u) x₀ ->
          Min (u₀ :: x₀) O u₀.
        Proof.
          intros u₀_le_x₀.
          split; [| easy].
          intros m w m_to_w.
          split.
            intros m_lt_O; contradict m_lt_O; apply Nat.nlt_0_r.
          destruct m as [| m']; intros m_gt_O.
            contradict m_gt_O; apply Nat.nlt_0_r.
          now apply u₀_le_x₀ with m'.
        Qed.

        Lemma cons_gt :
          u₀ > v ->
          Min x₀ n v ->
          Min (u₀ :: x₀) (S n) v.
        Proof.
          intros not_u₀_le_x₀ Min_n_v.
          split; [| apply Min_n_v].
          apply ForNth.cons; [split; order|].
          intros m w m_to_w.
          now unfold gt; rewrite <- 2!Nat.succ_lt_mono;
            apply Min_n_v.
        Qed.
      End Properties.

      Fixpoint minimum_body
        (x : list t)
        (index : nat)
        (n : nat)
        (v : t) :
        nat * t :=
        match x with
        | [] => (n, v)
        | u₀ :: x₀ =>
          if u₀ <? v then
            minimum_body x₀ (S index) index u₀
          else
            minimum_body x₀ (S index) n v
        end.

      Definition minimum
        (x : list t) :
        option (nat * t) :=
        match x with
        | [] => None
        | u₀ :: x₀ => Some (minimum_body x₀ 1 O u₀)
        end.

      Notation Minimum
        x
        n
        v :=
        (minimum x = Some (n, v)).

      Lemma minimum_body_spec : forall
        (x : list t)
        (index : nat)
        (n : nat)
        (v : t),
        let (n', v') := minimum_body x index n v in
        (v' <= v) /\
        ((n' = n /\
        v' = v /\
        ForNth (fun (m : nat) (w : t) => v' <= w) x) \/
        (v' < v /\
          exists m : nat,
            n' = index + m /\
            Min x m v')).
      Proof.
        induction x as [| u₀ x₀ IHx₀]; intros index n v.
          split; [| left].
            reflexivity.
            split; [easy|].
            split; [easy|].
            apply ForNth.nil.
        simpl; destruct (ltb_spec u₀ v) as [u₀_lt_v| u₀_ge_v].
          specialize (IHx₀ (S index) index u₀).
          destruct (minimum_body x₀ (S index) index u₀) as [n' v'],
            IHx₀ as [v'_le_u₀ IHx₀].
          split; [transitivity u₀; order|].
          destruct IHx₀ as [(-> & -> & u₀_le_x₀)| (v'_lt_u₀ & m' & IHx₀)]; right.
            split; [easy|].
            now exists O; split; [rewrite Nat.add_0_r| apply cons_le].
          split; [now transitivity u₀|].
          now exists (S m'); split;
            [rewrite Nat.add_succ_r| apply cons_gt, IHx₀].
        specialize (IHx₀ (S index) n v).
        destruct (minimum_body x₀ (S index) n v) as [n' v'],
          IHx₀ as [v'_le_u₀ IHx₀].
        split; [easy|].
        destruct IHx₀
          as [(n'_eq_n & v'_eq_v & v'_le_x₀)| (v'_lt_v & m' & IHx₀)];
          [left| right].
          repeat split; try easy.
          now apply ForNth.cons; [order|].
        split; [order|].
        now exists (S m'); split;
          [rewrite Nat.add_succ_r| apply cons_gt; [order|]].
      Qed.

      Lemma minimum_spec : forall x : list t,
        OptionSpec (fun min : nat * t => let (n, v) := min in Min x n v) (x = []) (minimum x).
      Proof.
        destruct x as [| u₀ x₀]; constructor.
          reflexivity.
        specialize minimum_body_spec with x₀ 1 O u₀ as IHx₀.
        destruct (minimum_body x₀ 1 O u₀) as (n' & v').
        now destruct IHx₀ as
          [_ [(-> & -> & IHx₀)| (v'_lt_u₀ & m' & -> & IHx₀)]];
          [apply cons_le| apply cons_gt].
      Qed.

      Section Properties.
        Variables
          (x : list t)
          (n : nat)
          (v : t).

        Lemma None_iff :
          minimum x = None <->
          x = [].
        Proof.
          clear n v.
          destruct (minimum_spec x) as [(n, v) (_ & n_to_v)| x_eq_nil];
            [destruct x as [| u₀ x₀]|]; try easy.
          now apply Nth.nil_inv in n_to_v.
        Qed.

        Lemma None_eq :
          minimum x = None ->
          x = [].
        Proof.
          apply None_iff.
        Qed.

        Lemma eq_None :
          x = [] ->
          minimum x = None.
        Proof.
          apply None_iff.
        Qed.

        Lemma Some_iff :
          Minimum x n v <->
          Min x n v.
        Proof.
          destruct (minimum_spec x) as [(n', v') Min_n'_v'| ->].
            split.
              now intros [= -> ->].
            intros Min_n_v.
            enough (n = n' /\ v = v') as (-> & ->) by easy.
            now apply Min_fun with x.
          unfold Min.
          now rewrite Nth.nil_iff.
        Qed.

        Lemma neq_Some :
          x <> [] ->
          exists
            (c : nat)
            (v : t),
            Minimum x c v /\
            Min x c v.
        Proof.
          clear n v.
          now destruct (minimum_spec x) as [(n & v) Min_n_v| ?];
            intros x_neq_nil;
            [exists n, v|].
        Qed.

        Lemma Some_neq :
          Minimum x n v ->
          Min x n v.
        Proof.
          apply Some_iff.
        Qed.
      End Properties.
    End Min.
    Module Min' := Min Nat.

    Notation add_S
      self
      p₀
      c₀ :=
      (Coloring.new
        (max (S c₀) self.(Coloring.colors))
        (Map.add p₀ c₀%nat self.(Coloring.labeling))).

    Fixpoint fixed_body
      (instructions : list Instruction.t)
      (coloring : Coloring.t)
      (counts : list nat) :
      option Coloring.t :=
      match instructions with
      | Up p₀ :: x₀ =>
        bind (Min'.minimum counts) (fun min => let (color, count) := min in
        bind (replace counts color (S count)) (fun counts' =>
          let coloring := add_S coloring p₀ color in
          fixed_body x₀ coloring counts'
          ))
      | Down p₀ :: x₀ =>
          bind (Coloring.find coloring p₀) (fun color =>
          bind (nth_error counts color) (fun count =>
          bind (pred_error count) (fun count' =>
          bind (replace counts color count') (fun counts' =>
            fixed_body x₀ coloring counts'))))
      | [] => ret coloring
      end.

    Definition fixed
      (instructions : Instructions.t)
      (colors : nat) :
      option Coloring.t :=
      fixed_body instructions Coloring.empty (repeat O colors).

    Lemma StronglyExtensional
      (coloring : Coloring.t) :
      forall p p' c c',
        Coloring.MapsTo coloring p c ->
        Coloring.MapsTo coloring p' c' ->
        c <> c' ->
        ~ Owner.eq p p'.
    Proof.
      intros p p' c c' p_to_c p'_to_c' c_neq_c'.
      contradict c_neq_c'; rewrite c_neq_c' in p_to_c.
      now apply MapsTo_fun with (1 := p_to_c).
    Qed.

    Module M := MSetWeakList.Make Owner.
    Module M_Facts := MSetFacts.Facts M.
    Module M_Properties := MSetProperties.WProperties M.

    Lemma add_eq_iff : forall
      (s : M.t)
      (x y : Owner.t),
      Owner.eq x y ->
        M.In y (M.add x s) <->
        True.
    Proof.
      intros.
      rewrite M_Facts.add_iff; tauto.
    Qed.

    Module State.
      Record t : Type := new {
        instructions : Instructions.t;
        coloring : Coloring.t;
        counts : list nat
      }.

      Inductive Fixed : relation State.t :=
      | Fixed_Up :
        forall
          (p₀ : Owner.t)
          (x₀ : Instructions.t)
          (coloring : Coloring.t)
          (counts counts' : list nat)
          (c₀ v₀ : nat),
          Min'.Min counts c₀ v₀ ->
          Replace.Ok counts c₀ (S v₀) counts' ->
          Fixed (new x₀ (add_S coloring p₀ c₀) counts') (new (Up p₀ :: x₀) coloring counts)
      | Fixed_Down :
        forall
          (p₀ : Owner.t)
          (x₀ : Instructions.t)
          (coloring : Coloring.t)
          (counts counts' : list nat)
          (c₀ v₀' : nat),
          Coloring.MapsTo coloring p₀ c₀ ->
          Nth counts c₀ (S v₀') ->
          Replace.Ok counts c₀ v₀' counts' ->
          Fixed (new x₀ coloring counts') (new (Down p₀ :: x₀) coloring counts).

      Module Ok.
        Section Ok.
          Variable
            (s : State.t).

          Definition Counts :
            Prop :=
            ForNth
              (fun (color count : nat) =>
              exists owners : M.t,
                (forall owner : Owner.t,
                M.In owner owners <->
                  Active owner s.(instructions) /\
                  Coloring.MapsTo s.(coloring) owner color) /\
                M.cardinal owners = count)
              s.(counts).

          Definition Length :
            Prop :=
            s.(coloring).(Coloring.colors) <= length s.(counts).

          Record t : Prop := new {
            instructions : Instructions.Ok s.(State.instructions);
            coloring : Coloring.Ok s.(State.coloring);
            synced : Synced s.(State.instructions) s.(State.coloring);
            counts : Counts;
            length : Length;
          }.

          Corollary counts_O :
            t ->
            forall
              color : nat,
              s.(State.coloring).(Coloring.colors) <= color < List.length s.(State.counts) ->
              Nth s.(State.counts) color 0.
          Proof.
            intros Ok_s c (colors_le_c & c_lt_counts).
            specialize NthError.lt_Some with (1 := c_lt_counts) as (v & c_to_v).
            enough (v = 0) as -> by easy.
            apply Ok_s.(counts) in c_to_v as (owners & Ok_owners & <-).
            enough (M.Empty owners) by
              now apply M_Properties.cardinal_Empty.
            intros p.
            enough (~ Coloring.MapsTo s.(State.coloring) p c) by
                now rewrite Ok_owners.
            enough (c_nlt_colors : ~ c < s.(State.coloring).(Coloring.colors)) by
              now contradict c_nlt_colors; apply Ok_s.(coloring); exists p.
            auto with arith.
          Qed.

          Corollary Min_le_colors :
            t ->
            forall
              c v : nat,
              Min'.Min s.(State.counts) c v ->
              c <= s.(State.coloring).(Coloring.colors).
          Proof with auto with arith.
            intros Ok_s c v (Min_c_v & c_to_v).
            enough (~ c > s.(State.coloring).(Coloring.colors)) by
              now apply not_gt.
            specialize Nat.nlt_0_r with v as c_gt_colors;
              contradict c_gt_colors.
            apply Min_c_v with (2 := c_gt_colors), counts_O...
            enough (s.(State.coloring).(Coloring.colors) < List.length s.(State.counts))...
            transitivity c;
              [| apply NthError.Some_lt with v]...
          Qed.
        End Ok.
      End Ok.

      Section Facts.
        Variables
          (s₀ s₁ : State.t)
          (Fixed_s₁_s₀ : Fixed s₁ s₀)
          (Ok_s₀ : Ok.t s₀).

        Let Ok_instructions₀ :
          Instructions.Ok s₀.(instructions) :=
          Ok_s₀.(Ok.instructions).
        Let Ok_coloring₀ :
          Coloring.Ok s₀.(coloring) :=
          Ok_s₀.(Ok.coloring).
        Let Synced_s₀ :
          Synced s₀.(instructions) s₀.(coloring) :=
          Ok_s₀.(Ok.synced).
        Let Ok_counts₀ :
          Ok.Counts s₀ :=
          Ok_s₀.(Ok.counts).
        Let Ok_length₀ :
          Ok.Length s₀ :=
          Ok_s₀.(Ok.length).

        Ltac destruct_Fixed :=
          destruct Fixed_s₁_s₀ as
          [p₀ x₀ coloring₀ counts₀ counts₁ c₀ v₀ (Min_c₀_v₀ & c₀_to_v₀) Replace_counts₁|
          p₀ x₀ coloring₀ counts₀ counts₁ c₀ v₀' p₀_to_c₀ c₀_to_v₀ Replace_counts₁];
          [apply Instructions.Ok.cons_Up_iff in Ok_instructions₀ as (Active_p₀_x₀ & Ok_x₀)| apply Instructions.Ok.cons_Down_iff in Ok_instructions₀ as (Absent_p₀_x₀ & Ok_x₀)].

        Let Pred_s₁_s₀ :
          Tail s₀.(instructions) s₁.(instructions).
        Proof.
          destruct_Fixed; constructor.
        Qed.

        Let Ok_instructions₁ :
          Instructions.Ok s₁.(instructions).
        Proof.
          pose proof (Ok_s₀.(Ok.instructions)).
          now rewrite <- Pred_s₁_s₀.
        Qed.

        Let Ok_coloring₁ :
          Coloring.Ok s₁.(coloring).
        Proof with my_auto.
          destruct_Fixed; cbn - [max] in *...
          assert (not_In_p₀ : ~ Coloring.Contains coloring₀ p₀).
            apply Synced_s₀...
          enough (c₀ < coloring₀.(Coloring.colors) \/ c₀ = coloring₀.(Coloring.colors)) as [c₀_lt_colors₀| ->].
              rewrite max_r; [apply Coloring.Ok.add_lt|]...
            rewrite max_l; [apply Coloring.Ok.add_eq|]...
          enough (c₀ <= coloring₀.(Coloring.colors)) by now apply le_lt_or_eq.
          now apply Ok.Min_le_colors with
            (s :=new (Up p₀ :: x₀) coloring₀ counts₀)
            (c := c₀)
            (v := v₀).
        Qed.

        Let Synced_s₁ :
          Synced s₁.(instructions) s₁.(coloring).
        Proof with (simpl; my_auto).
          destruct_Fixed;
            intros p; split; simpl.
                intros Active_p_x₀; apply add_in_iff.
                destruct (Owner.eq_dec p₀ p) as [p₀_eq_p| p₀_neq_p];
                  [left| right; apply Synced_s₀]...
              intros Ahead_p₀_x₀.
              apply add_not_in_iff; split...
              apply Synced_s₀...
            intros Active_p_x₀; apply Synced_s₀...
          intros Ahead_p_x₀; apply Synced_s₀...
        Qed.

        Let length_eq :
          length s₁.(counts) = length s₀.(counts).
        Proof.
          symmetry; destruct_Fixed; apply Replace_counts₁.
        Qed.

        Let Ok_length₁ :
          Ok.Length s₁.
        Proof with auto.
          unfold Ok.Length; rewrite length_eq.
          destruct_Fixed...
          apply Nat.max_lub...
          simpl; apply NthError.Some_lt with v₀...
        Qed.

        Let Ok_counts₁ :
          Ok.Counts s₁.
        Proof with (simpl; my_auto).
          unfold Ok.Counts, ForNth in Ok_counts₀.
          destruct_Fixed.
            intros c v c_to_v.
            destruct Replace_counts₁ as
              (c₀_lt_counts₀ & _ & c₀_to_S_v₀ & H).
            destruct (Nat.eq_dec c c₀) as [->| c_neq_c₀].
              specialize Ok_counts₀ with (1 := c₀_to_v₀) as
                (owners & owners_iff & owners_length).
              exists (M.add p₀ owners); simpl in *; split.
                intro p; destruct (Owner.eq_dec p₀ p) as
                  [p₀_eq_p| p₀_neq_p].
                  symmetry in p₀_eq_p.
                  now rewrite
                    add_eq_iff,
                    add_eq_mapsto_iff,
                    p₀_eq_p.
                now rewrite
                  M_Facts.add_neq_iff,
                  owners_iff,
                  add_neq_mapsto_iff,
                  Instructions.Active.cons_Up_neq_iff.
              rewrite M_Properties.add_cardinal_2, owners_length.
                now enough (Some (S v₀) = Some v) as [=];
                  [| transitivity (nth_error counts₁ c₀)].
              enough (~ Active p₀ (Up p₀ :: x₀)) by
                (rewrite owners_iff; tauto).
              enough (Owner.eq p₀ p₀) by
                (rewrite Instructions.Active.cons_Up_iff; tauto).
              reflexivity.
            specialize Ok_counts₀ with c v as
              (owners & owners_iff & owners_length);
              [now rewrite H|].
            exists owners; split; [| assumption].
            intros p; simpl in *.
            rewrite owners_iff.
            split; intros (Active_p & p_to_c).
              enough (~ Owner.eq p₀ p) by
              now rewrite
                <- Instructions.Active.cons_Up_neq_iff with (p₀ := p₀),
                add_neq_mapsto_iff...
              now apply Instructions.Active.cons_Up_iff in Active_p.
            apply add_mapsto_iff in p_to_c as
              [(_ & c₀_eq_c)| (p₀_neq_p & p_to_c₀)];
              [now contradict c_neq_c₀|].
            split...
          simpl in *.
          intros c v' c_to_v'.
          assert (c_lt_counts₀ : c < length counts₀).
            rewrite <- length_eq.
            now apply NthError.Some_lt with v'.
          specialize NthError.lt_Some with (1 := c_lt_counts₀) as
            (v & c_to_v).
          destruct Replace_counts₁ as
            (c₀_lt_counts₀ & _ & c₀_to_v₀' & H).
          specialize Ok_counts₀ with (1 := c_to_v) as
            (owners & owners_iff & owners_length).
          destruct (Nat.eq_dec c c₀) as [->| c_neq_c₀].
            2: {
              exists owners.
              assert (Some v = Some v') as [= <-] by
                now rewrite <- c_to_v, <- c_to_v'; apply H.
              split; [| assumption].
              intros p.
              rewrite owners_iff, Instructions.Active.cons_Down_iff...
              enough (Coloring.MapsTo coloring₀ p c -> ~ Owner.eq p₀ p) by tauto.
              intros p_to_c.
              now apply StronglyExtensional with coloring₀ c₀ c;
                [..| change (complement Logic.eq c₀ c)].
            }
          exists (M.remove p₀ owners); split.
            intros p.
            rewrite
              M.remove_spec,
              owners_iff,
              Instructions.Active.cons_Down_iff...
            enough ((Owner.eq p₀ p \/ Active p x₀) /\
            ~ Owner.eq p p₀ <-> Active p x₀) by firstorder.
            assert (Owner.eq p₀ p <-> Owner.eq p p₀) as -> by easy.
            enough (Active p x₀ -> ~ Owner.eq p p₀); [tauto|]...
          change (pred (S (M.cardinal (M.remove p₀ owners))) = v').
          rewrite M_Properties.remove_cardinal_1, owners_length; [| apply owners_iff]...
          enough (Some v = Some (S v₀') /\ Some v' = Some v₀') as
            ([= ->] & [= ->]) by reflexivity.
          now rewrite <- c_to_v, <- c₀_to_v₀, <- c_to_v', <- c₀_to_v₀'.
        Qed.

        Lemma Ok_s₁ :
          Ok.t s₁.
        Proof.
          now constructor.
        Qed.
      End Facts.
    End State.

    Definition Graph :=
      clos_refl_trans_n1 _ State.Fixed.

    Inductive Graph_Contains (s' : State.t) :
      forall s : State.t,
      Graph s' s ->
      State.t ->
      Prop :=
    | Contains_rtn1_refl :
      Graph_Contains (rtn1_refl State.t State.Fixed s') s'
    | Contains_rtn1_trans_left :
      forall
        (s₀ s₁ : State.t)
        (Fixed_s₁_s₀ : State.Fixed s₁ s₀)
        (Graph_s'_s₁ : Graph s' s₁),
        Graph_Contains (rtn1_trans _ _ _ _ _ Fixed_s₁_s₀ Graph_s'_s₁) s₀
    | Contains_rtn1_trans_right :
      forall
        (s₀ s₁ r : State.t)
        (Fixed_s₁_s₀ : State.Fixed s₁ s₀)
        (Graph_s'_s₁ : Graph s' s₁),
        Graph_Contains Graph_s'_s₁ r ->
        Graph_Contains (rtn1_trans _ _ _ _ _ Fixed_s₁_s₀ Graph_s'_s₁) r.

    Instance Fixed_Graph_subrelation :
      subrelation State.Fixed Graph.
    Proof.
      intros s' s Fixed_s'_s.
      now apply clos_rtn1_step.
    Qed.

    Generalizable Variables A R f.

    Instance Graph_morphism
      `{PreOrder_R : @PreOrder A R}
      `{Proper_f : Proper _ (State.Fixed --> R) f} :
      Proper (Graph --> R) f.
    Proof.
      intros s s'; induction 1 as [| s₀ s₁ Fixed_s₁_s₀]; [reflexivity|].
      now transitivity (f s₀);
        [rewrite Fixed_s₁_s₀|].
    Qed.

    Add Parametric Relation : Prop impl
      reflexivity proved by impl_Reflexive
      transitivity proved by impl_Transitive
      as PreOrder_impl.

    Add Parametric Morphism : State.Ok.t with signature
      State.Fixed --> impl as Ok_morphism.
    Proof.
      intros s₀ s₁ Fixed_s₁_s₀ Ok_s₀.
      now apply State.Ok_s₁ with s₀.
    Qed.

    Add Parametric Morphism : (compose (length (A := nat)) State.counts) with signature
      State.Fixed ++> eq as length_morphism.
    Proof.
      intros s₁ s₀ Fixed_s₁_s₀.
      symmetry; destruct Fixed_s₁_s₀ as
        [p₀ x₀ coloring₀ counts₀ counts₁ c₀ v₀ (Min_c₀_v₀ & c₀_to_v₀) Replace_counts₁|
        p₀ x₀ coloring₀ counts₀ counts₁ c₀ v₀' p₀_to_c₀ c₀_to_v₀ Replace_counts₁];
        apply Replace_counts₁.
    Qed.

    Add Parametric Morphism : State.instructions with signature
      State.Fixed --> Tail (A := Instruction.t) as instructions_morphism.
    Proof.
      intros v₀ v₁ Counter_v₁_v₀.
      induction Counter_v₁_v₀; constructor.
    Qed.

    Lemma coloring_morphism :
      forall
        s₀ s₁ : State.t,
        State.Ok.t s₀ ->
        State.Fixed s₁ s₀ ->
        Coloring.le s₀.(State.coloring) s₁.(State.coloring).
    Proof with my_auto.
      intros s₀ s₁ Ok_s₀ Fixed_s₁_s₀.
      destruct Fixed_s₁_s₀ as
        [p₀ x₀ coloring₀ counts₀ counts₁ c₀ v₀ (Min_c₀_v₀ & c₀_to_v₀) Replace_counts₁|
        p₀ x₀ coloring₀ counts₀ counts₁ c₀ v₀' p₀_to_c₀ c₀_to_v₀ Replace_counts₁].
        split.
          cbn - [max]; auto with arith.
        cbn; intros p c p_to_c.
        apply Map.add_2 with (2 := p_to_c).
        contradict p_to_c; rewrite <- p_to_c.
        enough (H : ~ Coloring.Contains coloring₀ p₀) by
          now contradict H; exists c.
        enough (Ahead p₀ (Up p₀ :: x₀)) by
          now apply Ok_s₀.(State.Ok.synced)...
      now split.
    Qed.

    Lemma Graph_coloring_morphism :
      forall
        s' s : State.t,
        State.Ok.t s ->
        Graph s' s ->
        Coloring.le s.(State.coloring) s'.(State.coloring).
    Proof with my_auto.
      intros s' s Ok_s Graph_s'_s.
      induction Graph_s'_s as [| s₁ s₀ Fixed_s₁_s₀ Graph_s'_s₁ IHs₁].
        reflexivity.
      now transitivity s₁.(State.coloring);
        [apply coloring_morphism| apply IHs₁; rewrite Fixed_s₁_s₀].
    Qed.

    Lemma fixed_body_spec :
      forall
        (instructions : Instructions.t)
        (coloring : Coloring.t)
        (counts : list nat)
        (s := State.new instructions coloring counts),
        State.Ok.t s ->
        length s.(State.counts) <> 0 ->
        exists s' : State.t,
          Graph s' s /\
          fixed_body instructions coloring counts = Some s'.(State.coloring).
    Proof with (simpl; my_auto).
      induction instructions as [| [[|] p₀] x₀ IHx₀];
        intros coloring₀ counts₀ s₀ Ok_s₀ counts₀_neq_nil.
          exists s₀; repeat constructor.
        simpl; destruct (Min'.minimum_spec counts₀) as
          [(c₀ & v₀) Min_c₀_v₀| counts_eq_nil];
          [| now apply length_zero_iff_nil in counts_eq_nil];
          simpl.
        specialize Replace.lt_Some with _ counts₀ c₀ (S v₀) as
          (counts₁ & -> & Replace_counts₁).
          apply NthError.Some_lt with v₀, Min_c₀_v₀.
        pose (s₁ := State.new x₀ (add_S coloring₀ p₀ c₀) counts₁).
        assert (Fixed_s₁_s₀ : State.Fixed s₁ s₀) by
          now constructor 1 with v₀.
        assert (Ok_s₁ : State.Ok.t s₁) by
          now rewrite Fixed_s₁_s₀.
        specialize IHx₀ with (1 := Ok_s₁) as
          (s' & Graph_s'_s₁ & H).
          change (compose (@length nat) State.counts s₁ <> 0).
          now rewrite Fixed_s₁_s₀.
        now exists s'; split;
          [constructor 2 with s₁|].
      assert (Active_p₀_s₀ : Active p₀ s₀.(State.instructions)) by
        (apply Instructions.Active.cons_Down_eq;
          [exact (Ok_s₀.(State.Ok.instructions))| reflexivity]).
      simpl; specialize find_In_Some as (c₀ & -> & p₀_to_c₀).
        now apply Ok_s₀.(State.Ok.synced).
      specialize NthError.lt_Some with _ counts₀ c₀ as
        (v₀ & c₀_to_v₀).
        apply lt_le_trans with s₀.(State.coloring).(Coloring.colors).
          now apply Ok_s₀.(State.Ok.coloring); exists p₀.
        apply Ok_s₀.(State.Ok.length).
      simpl; rewrite c₀_to_v₀; simpl.
      specialize Pred.neq_Some with v₀ as
        (v₀' & -> & Ok_v₀_v₀').
        specialize Ok_s₀.(State.Ok.counts) as
          (owners₀ & owners₀_iff & owners₀_length).
          exact c₀_to_v₀.
        rewrite <- owners₀_length, <- M_Properties.cardinal_Empty.
        now enough (In_p₀_owners₀ : M.In p₀ owners₀);
          [contradict In_p₀_owners₀| apply owners₀_iff].
      simpl; specialize Replace.lt_Some with _ counts₀ c₀ v₀' as
        (counts₁ & -> & Replace_counts₁).
        now apply NthError.Some_lt with v₀.
      pose (s₁ := State.new x₀ coloring₀ counts₁).
      assert (Fixed_s₁_s₀ : State.Fixed s₁ s₀) by
        now rewrite Ok_v₀_v₀' in c₀_to_v₀; constructor 2 with c₀ v₀'.
      assert (Ok_s₁ : State.Ok.t s₁).
        now rewrite Fixed_s₁_s₀.
      specialize IHx₀ with (1 := Ok_s₁) as
        (s' & Graph_s'_s₁ & H).
        change (compose (@length nat) State.counts s₁ <> 0).
        now rewrite Fixed_s₁_s₀.
      now exists s'; split;
        [constructor 2 with s₁|].
    Qed.

    Lemma Ahead_impl_Contains :
    forall
      s' s : State.t,
      s'.(State.instructions) = [] ->
      Graph s' s ->
      State.Ok.t s ->
      forall p : Owner.t,
        Ahead p s.(State.instructions) ->
        Coloring.Contains s'.(State.coloring) p.
    Proof with (simpl; my_auto).
      intros s' s instructions'_eq_nil.
      induction 1 as [| s₁ s₀ Fixed_s₁_s₀ Graph_s'_s₁ IHs₁];
        intros Ok_s₀ p Ahead_p;
        [| assert(Ok_s₁ : State.Ok.t s₁) by now rewrite Fixed_s₁_s₀].
        contradict Ahead_p; rewrite instructions'_eq_nil...
      specialize Tail.inv with _ s₁.(State.instructions) s₀.(State.instructions)
        as [([|] & p₀) H];
        [now apply instructions_morphism| rewrite H in Ahead_p..].
        apply Instructions.Ahead.cons_Up_iff in Ahead_p as [<-| Ahead_p].
          enough (Coloring.Contains s₁.(State.coloring) p₀) as (c & p_to_c) by
            now exists c; apply Graph_coloring_morphism with (2 := Graph_s'_s₁).
          apply Ok_s₁.(State.Ok.synced), Instructions.Ok.cons_Up_iff.
          replace (Up p₀ :: s₁.(State.instructions)) with
            (s₀.(State.instructions)).
          now apply State.Ok.instructions.
        now apply IHs₁.
      apply Instructions.Ahead.cons_Down_iff in Ahead_p.
      now apply IHs₁.
    Qed.

    Module Assumptions.
      Import MSets.

      Module M := MSetWeakList.Make Owner.
      Module Import M_Facts := MSetFacts.Facts M.
      Module Import M_Properties := MSetProperties.WProperties M.

      Lemma add_eq_iff : forall
        (s : M.t)
        (x y : Owner.t),
        Owner.eq x y ->
          M.In y (M.add x s) <->
          True.
      Proof.
        intros.
        rewrite add_iff; tauto.
      Qed.

      Module Count.
        Definition Ok
          (instructions : Instructions.t)
          (coloring : Coloring.t)
          (color : nat)
          (count : nat) :
          Prop :=
          exists owners : M.t,
            (forall owner : Owner.t,
              M.In owner owners <->
                Active owner instructions /\
                Coloring.MapsTo coloring owner color) /\
            M.cardinal owners = count.
      End Count.

      Definition Ok
        (instructions : Instructions.t)
        (coloring : Coloring.t)
        (counts : list nat) :
        Prop :=
        Instructions.Ok instructions /\
        Coloring.Ok coloring /\
        (coloring.(Coloring.colors) <= length counts /\ length counts <> O) /\
        Synced instructions coloring /\
        ForNth (Count.Ok instructions coloring) counts /\
        (forall color : nat,
          coloring.(Coloring.colors) <= color < length counts ->
          Nth counts color 0).

      Ltac Ok_destruct ok :=
        destruct ok as
          (Ok_instructions &
          Ok_coloring &
          (Ok_length & length_neq_O) &
          Synced_coloring &
          Ok_counts &
          Ok_zero).

      Lemma cons_Down : forall
        (p₀ : Owner.t)
        (x₀ : Instructions.t)
        (coloring : Coloring.t)
        (counts : list nat),
        Ok (Down p₀ :: x₀) coloring counts ->
        exists
          (c₀ : nat)
          (v₀ : nat)
          (v₀' : nat)
          (counts' : list nat),
          Coloring.MapsTo coloring p₀ c₀ /\
          Nth counts c₀ v₀ /\
          Pred v₀ v₀' /\
          Pred.Ok v₀ v₀' /\
          List.Replace.Replace counts c₀ v₀' counts' /\
          Replace.Ok counts c₀ v₀' counts' /\
          Ok x₀ coloring counts'.
      Proof with my_auto.
        intros p₀ x₀ coloring counts ok.
        Ok_destruct ok.

        assert (Ok_x₀ : Instructions.Ok x₀) by
          now apply Instructions.Ok.cons_inv with (Down p₀).
        assert (Active_p₀_x : Active p₀ (Down p₀ :: x₀))...
        assert (Absent_p₀_x₀ : Absent p₀ x₀)...

        assert (In_p₀ : Coloring.Contains coloring p₀).
          apply Synced_coloring...
        specialize find_In_Some with (1 := In_p₀) as (c₀ & _ & p₀_to_c₀);
          exists c₀.

        assert (c₀_lt_colors : c₀ < coloring.(Coloring.colors)) by
          now apply Ok_coloring; exists p₀.
        assert (c₀_lt_counts : c₀ < length counts) by
          now apply lt_le_trans with coloring.(Coloring.colors).
        specialize NthError.lt_Some with (1 := c₀_lt_counts) as
          (v₀ & c₀_to_v₀);
          exists v₀.

        unfold ForNth in Ok_counts.
        pose proof Ok_counts as H;
          specialize H with (1 := c₀_to_v₀) as
          (owners₀ & owners₀_iff & owners₀_length).
        assert (p₀_in_owners₀ : M.In p₀ owners₀) by
          now apply owners₀_iff.

        assert (v₀_neq_O : v₀ <> O).
          rewrite <- owners₀_length, <- cardinal_Empty.
          now contradict p₀_in_owners₀.
        specialize Pred.neq_Some with (1 := v₀_neq_O) as
          (v₀' & pred_v₀_v₀' & Ok_v₀_v₀');
          exists v₀'.

        specialize Replace.lt_Some with (x := counts) (1 := c₀_lt_counts) (v := v₀') as
          (counts' & replace_counts' & Ok_counts');
          exists counts'.

        destruct Ok_counts' as (_ & length_counts' & c₀_to_v₀' & H).

        split_left; try assumption.
                now split_left.

              now rewrite <- length_counts'.

            split; intros ?; apply Synced_coloring...

          intros c v' c_to_v'.
          assert (c_lt_counts : c < length counts).
            rewrite length_counts'.
            now apply NthError.Some_lt with v'.
          specialize NthError.lt_Some with (1 := c_lt_counts) as
            (v & c_to_v).
          unfold ForNth in Ok_counts.
          specialize Ok_counts with (1 := c_to_v) as
            (owners & owners_iff & owners_length).
          destruct (Nat.eq_dec c c₀) as [->| c_neq_c₀].
            2: {
              exists owners.
              assert (Some v = Some v') as [= <-] by
                now rewrite <- c_to_v, <- c_to_v'; apply H.
              split; [| assumption].
              intros p.
              rewrite owners_iff, Instructions.Active.cons_Down_iff by
                assumption.
              enough (Coloring.MapsTo coloring p c -> ~ Owner.eq p₀ p) by tauto.
              intros p_to_c.
              now apply StronglyExtensional with coloring c₀ c;
                [..| change (complement Logic.eq c₀ c)].
            }
            exists (M.remove p₀ owners); split.
              intros p.
              rewrite
                M.remove_spec,
                owners_iff,
                Instructions.Active.cons_Down_iff by assumption.
              enough ((Owner.eq p₀ p \/ Active p x₀) /\
              ~ Owner.eq p p₀ <-> Active p x₀) by firstorder.
              assert (Owner.eq p₀ p <-> Owner.eq p p₀) as -> by easy.
              enough (Active p x₀ -> ~ Owner.eq p p₀); [tauto|]...
            change (pred (S (M.cardinal (M.remove p₀ owners))) = v').
            rewrite remove_cardinal_1, owners_length; [| apply owners_iff]...
            enough (Some v = Some v₀ /\ Some v' = Some (pred v₀)) as
              ([= ->] & [= ->]) by reflexivity.
            now rewrite <- c_to_v, <- c_to_v', c₀_to_v₀, c₀_to_v₀', Ok_v₀_v₀'.

          intros c (colors_le_c & c_lt_counts').
          rewrite <- (H c).
            now apply Ok_zero; rewrite length_counts'.
          change (complement Logic.eq c c₀); symmetry.
          now apply Nat.lt_neq, lt_le_trans with coloring.(Coloring.colors).
        Qed.

        Lemma cons_Up : forall
          (p₀ : Owner.t)
          (x₀ : Instructions.t)
          (coloring : Coloring.t)
          (counts : list nat),
          Ok (Up p₀ :: x₀) coloring counts ->
          exists
            (c₀ : nat)
            (v₀ : nat)
            (counts' : list nat),
            let coloring' := add_S coloring p₀ c₀ in
            Min'.Minimum counts c₀ v₀ /\
            Min'.Min counts c₀ v₀ /\
            List.Replace.Replace counts c₀ (S v₀) counts' /\
            Replace.Ok counts c₀ (S v₀) counts' /\
            Ok x₀ coloring' counts'.
        Proof with my_auto.
          intros p₀ x₀ coloring counts ok.
          Ok_destruct ok.
          set (labeling := coloring.(Coloring.labeling)) in *.
          set (colors := coloring.(Coloring.colors)) in *.

          assert (Ok_x₀ : Instructions.Ok x₀) by
            now apply Instructions.Ok.cons_inv with (Up p₀).
          assert (Ahead_p₀_x : Ahead p₀ (Up p₀ :: x₀))...
          assert (Active_p₀_x₀ : Active p₀ x₀)...

          assert (counts_neq_nil : counts <> []) by
            now rewrite <- length_zero_iff_nil.

          specialize Min'.neq_Some with (1 := counts_neq_nil) as
            (c₀ & v₀ & Minimum_c₀_v₀ & Min_v₀ & c₀_to_v₀);
            exists c₀, v₀.

          assert (c₀_lt_counts : c₀ < length counts) by
            now apply NthError.Some_lt with v₀.
          assert (c₀_le_colors : c₀ <= colors).
            apply not_gt.
            specialize Nat.nlt_0_r with v₀ as c₀_gt_colors; contradict c₀_gt_colors.
            assert (colors_to_0 : Nth counts colors O) by
              now apply Ok_zero; split; [| transitivity c₀].
            now apply Min_v₀ with (1 := colors_to_0).
          assert (not_In_p₀ : ~ Coloring.Contains coloring p₀).
            apply Synced_coloring...
          assert (max_r : c₀ < colors -> Init.Nat.max (S c₀) colors = colors).
            now intros c₀_lt_colors; apply Nat.max_r.
          assert (max_l : c₀ = colors -> Init.Nat.max (S c₀) colors = S colors).
            now intros ->; apply Nat.max_l, Nat.le_succ_diag_r.

          specialize Replace.lt_Some with (v := S v₀) (1 := c₀_lt_counts) as
            (counts' & -> & _ & length_counts' & c₀_to_S_v₀ & H);
            exists counts'.
          split_left; try easy.
                  apply le_lt_or_eq in c₀_le_colors as
                    [c₀_lt_colors| ->].
                    rewrite max_r; [apply Coloring.Ok.add_lt|]...
                  rewrite max_l; [apply Coloring.Ok.add_eq|]...
                now rewrite <- length_counts'; split; [apply Nat.max_lub|].

              intros p; split.
              intros Active_x₀; apply add_in_iff.
              destruct (Owner.eq_dec p₀ p) as [p₀_eq_p| p₀_neq_p];
                [left| right; apply Synced_coloring]...
              intros Ahead_p.
              apply add_not_in_iff; split...
              apply Synced_coloring...

            intros c v c_to_v.
            destruct (Nat.eq_dec c c₀) as [->| c_neq_c₀].
              unfold ForNth in Ok_counts.
              specialize Ok_counts with (1 := c₀_to_v₀) as
              (owners & owners_iff & owners_length).

              exists (M.add p₀ owners); split.
                unfold labeling in *.
                simpl in *.

                intro p; destruct (Owner.eq_dec p₀ p) as
                  [p₀_eq_p| p₀_neq_p].
                  symmetry in p₀_eq_p.
                  now rewrite
                    add_eq_iff,
                    add_eq_mapsto_iff,
                    p₀_eq_p.
                now rewrite
                  add_neq_iff,
                  owners_iff,
                  add_neq_mapsto_iff,
                  Instructions.Active.cons_Up_neq_iff.
              rewrite add_cardinal_2, owners_length.
                now enough (Some (S v₀) = Some v) as [=];
                  [| transitivity (nth_error counts' c₀)].
              assert (In_p₀ : Owner.eq p₀ p₀) by reflexivity;
                contradict In_p₀.
              enough (Active p₀ (Up p₀ :: x₀));
                [| apply owners_iff]...
            unfold Count.Ok, ForNth in *.
            specialize Ok_counts with c v as
            (owners & owners_iff & owners_length);
              [now rewrite H|].
            exists owners; split; [| assumption].
            intros p; simpl.
            rewrite owners_iff.
            split; intros (Active_p & p_to_c).
              enough (~ Owner.eq p₀ p) by
              now rewrite
                <- Instructions.Active.cons_Up_neq_iff with (p₀ := p₀),
                add_neq_mapsto_iff...
            apply add_mapsto_iff in p_to_c as
              [(_ & c₀_eq_c)| (p₀_neq_p & p_to_c₀)];
              [now contradict c_neq_c₀|].
            split...

          rewrite <- length_counts'.
          intros c (colors'_le_c₀ & c₀_lt_counts').
          apply le_lt_or_eq in c₀_le_colors as
            [c₀_lt_colors| c₀_eq_colors].
            rewrite max_r in colors'_le_c₀ by assumption; simpl in colors'_le_c₀.
            rewrite <- (H c).
              now apply Ok_zero.
            enough (c₀ <> c) by auto with arith.
            now apply Nat.lt_neq, lt_le_trans with colors.
          rewrite max_l in colors'_le_c₀ by assumption; simpl in colors'_le_c₀.
          rewrite <- (H c).
            apply Ok_zero; auto with arith.
          rewrite c₀_eq_colors.
          enough (colors <> c) by auto with arith.
          now apply Nat.lt_neq.
        Qed.
    End Assumptions.

    Module Type Proposition.
      Parameter t :
        Instructions.t ->
        Coloring.t ->
        list nat ->
        option Coloring.t ->
        Prop.
    End Proposition.

    Module Type BaseCase (P : Proposition).
      Section Basis.
        Variables
          (coloring : Coloring.t)
          (counts : list nat).

        Parameter nil :
          Assumptions.Ok [] coloring counts ->
          P.t [] coloring counts (Some coloring).
      End Basis.
    End BaseCase.

    Module Type InductionSteps (P : Proposition).
      Section Steps.
        Variables
          (p₀ : Owner.t)
          (x₀ : Instructions.t)
          (coloring : Coloring.t)
          (counts counts' : list nat)
          (c₀ v₀ v₀' : nat)
          (result : option Coloring.t).

        Parameter cons_Up :
          Assumptions.Ok (Up p₀ :: x₀) coloring counts ->
          Min'.Min counts c₀ v₀ ->
          List.Replace.Ok counts c₀ (S v₀) counts' ->
          P.t x₀ (add_S coloring p₀ c₀) counts' result ->
          P.t (Up p₀ :: x₀) coloring counts result.

        Parameter cons_Down :
          Assumptions.Ok (Down p₀ :: x₀) coloring counts ->
          Pred.Ok v₀ v₀' ->
          List.Replace.Ok counts c₀ v₀' counts' ->
          P.t x₀ coloring counts' result ->
          P.t (Down p₀ :: x₀) coloring counts result.
      End Steps.
    End InductionSteps.

    Module Type Steps := Proposition <+ BaseCase <+ InductionSteps. (* TODO *)

    Module InductionPrinciple (P : Proposition) (B : BaseCase P) (S : InductionSteps P).
      Lemma ind :
        forall
          (instructions : Instructions.t)
          (coloring : Coloring.t)
          (counts : list nat),
          Assumptions.Ok
            instructions
            coloring
            counts ->
          P.t
            instructions
            coloring
            counts
            (fixed_body instructions coloring counts).
      Proof.
        induction instructions as [| ([|] & p₀) x₀ IHx₀];
          intros coloring counts ok.
            now apply B.nil.
          simpl; unfold bind.
          specialize Assumptions.cons_Up with (1 := ok) as
            (c₀ & v₀ & counts' & -> & Ok_c₀_v₀ & -> & Ok_counts' & ok').
          specialize IHx₀ with (1 := ok').
          now apply S.cons_Up with counts' c₀ v₀.
        simpl; unfold bind.
        specialize (Assumptions.cons_Down) with (1 := ok) as
          (c₀ & v₀ & v₀' & counts' & p₀_to_c₀ & H).
        rewrite Map.find_1 with (1 := p₀_to_c₀).
        destruct H as (-> & -> & ? & -> & Ok_counts' & ok').
        specialize IHx₀ with (1 := ok').
        now apply S.cons_Down with counts' c₀ v₀ v₀'.
      Qed.
    End InductionPrinciple.
  End Fixed.
End Make.

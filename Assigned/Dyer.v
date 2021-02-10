Set Implicit Arguments.

Require Import Coq.Structures.Equalities Coq.Structures.EqualitiesFacts.
Require Import Coq.Structures.Orders Coq.Structures.OrdersFacts.

Require Import Coq.Lists.SetoidList.
Import ListNotations.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Arith.Arith.

Require Coq.MSets.MSets.
Require Import Coq.FSets.FMaps.

Require Import Shuffle.Misc.
Require Import Shuffle.List.
Require Shuffle.Assigned.Instructions.
Require Import Shuffle.Coloring.

Module WFacts_fun' (Key : DecidableType) (Import Map : WSfun Key).
  Include WFacts_fun Key Map.

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
    destruct (find x m) eqn: find; constructor.
      now apply find_mapsto_iff.
    now apply not_find_in_iff.
  Qed.

  Lemma add_eq_mapsto_iff : forall
    [elt : Type]
    (m : Map.t elt)
    (x y : Map.key)
    (e e' : elt),
    Key.eq x y ->
      MapsTo y e' (add x e m) <->
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

Module Make (Owner : DecidableTypeBoth) (Map : WSfun Owner).
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

    Fixpoint regular
      (instructions : list Instruction.t)
      (coloring : Coloring.t)
      (unused_colors : list nat) :
      option Coloring.t :=
      match instructions, unused_colors with
      | Up owner :: tail, [] =>
        regular
          tail
          (Coloring.add_eq coloring owner)
          []
      | Up owner :: tail, color :: unused_colors =>
        regular
          tail
          (Coloring.add_lt coloring owner color)
          unused_colors
      | Down owner :: tail, unused_colors =>
          bind(Coloring.find coloring owner) (fun color =>
          regular
            tail
            coloring
            (color :: unused_colors))
      | [], _ => ret coloring
      end.

    Module Type AssumptionType.
      Parameter Ok : list Instruction.t -> Coloring.t -> list nat -> Prop.

      Section Properties.
        Variable owner : Owner.t.
        Variable instructions : list Instruction.t.
        Variable coloring : Coloring.t.
        Variable color : nat.
        Variable unused_colors : list nat.
        Variable result : option Coloring.t.

        Parameter cons_Up_eq :
          Ok (Up owner :: instructions) coloring [] ->
          Ok instructions (Coloring.add_eq coloring owner) [].

        Parameter cons_Up_lt :
          Ok (Up owner :: instructions) coloring (color :: unused_colors) ->
          Ok instructions (Coloring.add_lt coloring owner color) unused_colors.

        Parameter cons_Down :
          Coloring.MapsTo coloring owner color ->
          Ok (Down owner :: instructions) coloring unused_colors ->
          Ok instructions coloring (color :: unused_colors).
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
        Variable owner : Owner.t.
        Variable instructions : list Instruction.t.
        Variable coloring : Coloring.t.
        Variable color : nat.
        Variable unused_colors : list nat.

        Lemma cons_Up_eq :
          Ok (Up owner :: instructions) coloring [] ->
          Ok instructions (Coloring.add_eq coloring owner) [].
        Proof with my_auto.
          intros ok; Ok_destruct ok.
          assert (not_In_owner : ~ Coloring.Contains coloring owner).
            apply Synced_coloring...
          unfold Ok.
          split_left...
                now apply Instructions.Ok.cons_inv in Ok_instructions.
              apply Coloring.Ok.add_eq, Synced_coloring...
            intros owner'.
            split.
              intros Active_owner'.
              apply add_in_iff.
              destruct (Owner.eq_dec owner owner') as [eq| neq];
                [left| right; apply Synced_coloring]...
            intros Ahead_owner.
            apply add_not_in, Synced_coloring...
            enough (Active owner instructions)...
          intros x y x_neq_y Active_x Active_y m n.
          simpl; rewrite ?add_mapsto_iff.
          intros
            [(owner_eq_x & <-)| (owner_neq_x & x_to_m)]
            [(owner_eq_y & <-)| (owner_neq_y & y_to_m)].
                now contradict x_neq_y; transitivity owner.
              enough (n <> Coloring.colors coloring) by firstorder.
              now apply Nat.lt_neq, Ok_coloring; exists y.
            now apply Nat.lt_neq, Ok_coloring; exists x.
          apply Proper_coloring with x y...
        Qed.

        Lemma cons_Up_lt :
          Ok (Up owner :: instructions) coloring (color :: unused_colors) ->
          Ok instructions (Coloring.add_lt coloring owner color) unused_colors.
        Proof with my_auto.
          intros ok; Ok_destruct ok.
          apply Forall_cons_iff in Ok_unused_colors as (Ok_color & Ok_unused_colors).
          apply NoDup_cons_iff in NoDup_unused_colors as (not_In_color & NoDup_unused_colors).
          assert (not_In_owner : ~ Coloring.Contains coloring owner).
            apply Synced_coloring...
          split_left...
                  now apply Instructions.Ok.cons_inv with (Up owner).
                apply Coloring.Ok.add_lt, Ok_coloring...
                destruct Ok_color as (_ & owner' & owner'_to_color & _).
                now exists owner'.
              intros owner'.
              split.
                intros Active_owner'.
                apply add_in_iff.
                destruct (Owner.eq_dec owner owner') as [eq| neq];
                  [left| right; apply Synced_coloring]...
              intros Ahead_owner.
              apply add_not_in, Synced_coloring; enough (Active owner instructions)...
            intros x y x_neq_y Active_x Active_y m n.
            simpl; rewrite ?add_mapsto_iff.
            intros
              [(owner_eq_x & <-)| (owner_neq_x & x_to_m)]
              [(owner_eq_y & <-)| (owner_neq_y & y_to_m)].
                  now contradict x_neq_y; transitivity owner.
                apply Ok_color with y...
                enough (color <> m) by firstorder.
              apply Ok_color with x...
            apply Proper_coloring with x y...
          eapply Forall_impl, Forall_and with (1 := Ok_unused_colors), not_In_Forall, not_In_color.
          intros n ((Proper_n & Synced_n) & color_neq_n).
          split.
            intros owner' n' Active_owner'.
            simpl; rewrite add_mapsto_iff.
            intros [(owner_eq_owner' & <-)| (owner_neq_owner' & owner'_to_n)].
              auto with arith.
            apply Proper_n with owner'...
          destruct Synced_n as (owner' & owner'_to_n & not_In_Down_owner').
          assert (owner_neq_owner': ~ Owner.eq owner owner').
            contradict not_In_Down_owner'; rewrite <- not_In_Down_owner'.
            apply Instructions.Orthogonal.Up_impl_Down...
          exists owner'; split...
          apply Map.add_2...
        Qed.

        Lemma cons_Down :
          Coloring.MapsTo coloring owner color ->
          Ok (Down owner :: instructions) coloring unused_colors ->
          Ok instructions coloring (color :: unused_colors).
        Proof with my_auto.
          intros owner_to_color (Ok_instructions & Ok_coloring & Synced_coloring & Real & Ok_unused_colors & NoDup_unused_colors).
          split_left...
                  now apply Instructions.Ok.cons_inv in Ok_instructions.
                intros owner'.
                split.
                  intros Active_owner'.
                  apply Synced_coloring...
                intros Ahead_owner'.
                apply Synced_coloring...
              intros x y x_neq_y Active_x Active_y m n x_to_m y_to_n.
              apply Real with x y...
            constructor.
              split.
                intros owner' color' Active_owner' owner'_to_color'.
                apply Real with owner owner'...
                enough (Absent owner instructions)...
              exists owner...
            eapply Forall_impl with (2 := Ok_unused_colors).
            intros n (H & owner' & owner'_to_color & not_InDown_owner').
            split.
              intros x m Active_x x_to_m.
              apply H with x...
            exists owner'...
          constructor...
          apply not_In_Forall, Forall_impl with (2 := Ok_unused_colors).
          intros n [Proper_n Synced_n].
          enough (n <> color) by auto with arith.
          apply Proper_n with owner...
        Qed.
      End Properties.
    End Assumption.

    Definition Synced'
      (instructions : list Instruction.t)
      (coloring result : Coloring.t) :=
      (forall (owner : Owner.t) (color : nat),
      ~ Ahead owner instructions ->
      Coloring.MapsTo result owner color ->
      Coloring.MapsTo coloring owner color).

    Lemma Ok_regular : forall
      (instructions : list Instruction.t)
      (coloring : Coloring.t)
      (unused_colors : list nat),
      Assumption.Ok instructions coloring unused_colors ->
      OptionSpec (fun result : Coloring.t =>
        Coloring.Ok result /\
        Subsets (RealColoring result) instructions /\
        Synced' instructions coloring result)
        False
        (regular instructions coloring unused_colors).
    Proof with my_auto.
      induction instructions as [| [[|] owner] instructions IHinstructions];
        intros coloring unused_colors ok.
            Ok_destruct ok.
          constructor; split_left...
          constructor.
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
            constructor...
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
          apply Map.add_3 with owner (Coloring.colors coloring),
            Synced_result...
        pose proof (ok' := Assumption.cons_Up_lt ok).
        specialize IHinstructions with (1 := ok').
        apply OptionSpec_impl with (2 := IHinstructions).
        intros result (Ok_result & Proper_result & Synced_result).
        Ok_destruct ok'.
        split_left...
          constructor...
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
      destruct (Coloring.find coloring owner) as [color|] eqn: find.
        apply find_mapsto_iff in find as owner_to_color.
        pose proof (ok' := Assumption.cons_Down owner_to_color ok).
        specialize IHinstructions with (1 := ok').
        apply OptionSpec_impl with (2 := IHinstructions).
        intros result (Ok_result & Proper_result & Synced_result).
        split_left...
          constructor...
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
      Ok_destruct ok.
      apply not_find_in_iff in find as not_In_owner; contradict not_In_owner.
      apply Synced_coloring...
    Qed.

    Definition color
      (instructions : list Instruction.t) :
      option Coloring.t :=
      regular instructions Coloring.empty [].

    Lemma Ok_color : forall
      (instructions : list Instruction.t),
      Instructions.Ok instructions ->
      (forall owner : Owner.t,
        In (Down owner) instructions -> Ahead owner instructions) ->
      OptionSpec (fun result =>
        Coloring.Ok result /\
        Subsets (RealColoring result) instructions)
        False
        (color instructions).
    Proof with my_auto.
      intros instructions Ok_instructions Down_impl_Up.
      eapply OptionSpec_impl, Ok_regular.
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

      Definition Min (x : list t) (n : nat) (v : t)  :=
        ForNth (fun (m : nat) (w : t) =>
          ((m < n)%nat -> v < w) /\
          ((m > n)%nat -> v <= w)) x /\
        Nth x n v.

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
    End Min.
    Module Min' := Min Nat.

    Fixpoint fixed
      (instructions : list Instruction.t)
      (coloring : Coloring.t)
      (counts : list nat) :
      option Coloring.t :=
      match instructions with
      | Up op₀ :: x₀ =>
        bind (Min'.minimum counts) (fun min => let (color, count) := min in
        bind (nth_error counts color) (fun count =>
        bind (replace counts color (S count)) (fun counts' => let coloring :=
            (max (S color) (Coloring.colors coloring), Map.add op₀ color (Coloring.labeling coloring)) in
          fixed x₀ coloring counts
          )))
      | Down op₀ :: x₀ =>
          bind (Coloring.find coloring op₀) (fun color =>
          bind (nth_error counts color) (fun count =>
          bind (replace counts color (pred count)) (fun counts =>
            fixed x₀ coloring counts)))
      | [] => ret coloring
      end.

    Definition Synced
      (instructions : list Instruction.t)
      (coloring : Coloring.t) :=
      forall owner : Owner.t,
        (Active owner instructions ->
        Coloring.Contains coloring owner) /\
        (Ahead owner instructions ->
        ~ Coloring.Contains coloring owner).

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

    Module Import M := MSetWeakList.Make Owner.
    Module Import M_Facts := MSetFacts.Facts M.
    Module Import M_Properties := MSetProperties.WProperties M.

    Definition Count_Ok
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
        cardinal owners = count.

    Module Assumptions.
      Definition Ok
        (instructions : Instructions.t)
        (coloring : Coloring.t)
        (counts : list nat) :
        Prop :=
        Instructions.Ok instructions /\
        Coloring.Ok coloring /\
        (Coloring.colors coloring <= length counts) /\
        Synced instructions coloring /\
        ForNth (Count_Ok instructions coloring) counts /\
        (forall color : nat,
          Coloring.colors coloring <= color < length counts ->
          Nth counts color 0).

      Ltac Ok_destruct ok :=
          destruct ok as
            (Ok_instructions &
            Ok_coloring &
            Ok_length &
            Synced_coloring &
            Ok_counts &
            Ok_zero).

      Lemma cons_Down : forall p₀ x₀ coloring counts,
        Ok (Down p₀ :: x₀) coloring counts ->
        OptionSpec
          (Ok x₀ coloring)
          False
          (
            bind (Coloring.find coloring p₀) (fun color =>
            bind (nth_error counts color) (fun count =>
            replace counts color (pred count)))
          ).
      Proof with my_auto.
        intros p₀ x₀ coloring counts ok.
        Ok_destruct ok.

        assert (Ok_x₀ : Instructions.Ok x₀) by
          now apply Instructions.Ok.cons_inv with (Down p₀).
        assert (Active_p₀_x : Active p₀ (Down p₀ :: x₀))...
        assert (Absent_p₀_x₀ : Absent p₀ x₀)...

        assert (In_p₀ : Coloring.Contains coloring p₀).
          apply Synced_coloring...
        destruct (find_spec (Coloring.labeling coloring) p₀) as
          [c₀ p₀_to_c₀| not_In_p₀];
          [| contradiction]; simpl.

        assert (c₀_lt_colors : c₀ < Coloring.colors coloring) by
          now apply Ok_coloring; exists p₀.
        assert (c₀_lt_counts : c₀ < length counts) by
          now apply lt_le_trans with (Coloring.colors coloring).
        specialize NthError.lt_Some with (1 := c₀_lt_counts) as
          (v₀ & c₀_to_v₀); rewrite c₀_to_v₀; simpl.
        unfold ForNth in Ok_counts.
        pose proof Ok_counts as H;
          specialize H with (1 := c₀_to_v₀) as
          (owners₀ & owners₀_iff & owners₀_length).
        specialize Replace.lt_Some with (x := counts) (1 := c₀_lt_counts) as
          (counts' & -> & _ & counts_eq_counts' & c₀_to_pred_v₀ & H₀').
        simpl.
        constructor; split_left.
                  assumption.
                assumption.
              now rewrite <- counts_eq_counts'.
            split; intros ?; apply Synced_coloring...
          intros c v' c_to_v'.
          assert (c_lt_counts : c < length counts).
            rewrite counts_eq_counts'.
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
                now rewrite <- c_to_v, <- c_to_v'; apply H₀'.
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
            change (pred (S (cardinal (remove p₀ owners))) = v').
            rewrite remove_cardinal_1, owners_length; [| apply owners_iff]...
            enough (Some v = Some v₀ /\ Some v' = Some (pred v₀)) as
              ([= ->] & [= ->]) by reflexivity.
            now rewrite <- c_to_v, <- c_to_v', c₀_to_v₀, c₀_to_pred_v₀.
          intros c (colors_le_c & c_lt_counts').
          rewrite <- (H₀' c).
            now apply Ok_zero; rewrite counts_eq_counts'.
          change (complement Logic.eq c c₀); symmetry.
          now apply Nat.lt_neq, lt_le_trans with (Coloring.colors coloring).
        Qed.

        Lemma add_eq_iff : forall s x y,  E.eq x y -> (In y (add x s) <-> True).
        Proof.
          intros.
          rewrite add_iff; tauto.
        Qed.

        Lemma cons_Up : forall p₀ x₀ coloring counts,
          counts <> [] ->
          Ok (Up p₀ :: x₀) coloring counts ->
          OptionSpec
            (fun H => Ok x₀ (fst H) (snd H))
            False
            (
              bind (Min'.minimum counts) (fun min => let (color, count) := min in
              bind (nth_error counts color) (fun count =>
              bind (replace counts color (S count)) (fun counts' => let coloring' :=
                  (max (S color) (Coloring.colors coloring), Map.add p₀ color (Coloring.labeling coloring)) in
                Some (coloring', counts'))))
            ).
        Proof with my_auto.
          intros p₀ x₀ coloring counts counts_neq_nil ok.
          Ok_destruct ok.
           set (labeling := Coloring.labeling coloring) in *.
          set (colors := Coloring.colors coloring) in *.

          assert (Ok_x₀ : Instructions.Ok x₀) by
            now apply Instructions.Ok.cons_inv with (Up p₀).
          assert (Ahead_p₀_x : Ahead p₀ (Up p₀ :: x₀))...
          assert (Active_p₀_x₀ : Active p₀ x₀)...

          destruct (Min'.minimum_spec counts) as [(c₀ & v₀) (Min_v₀ & c₀_to_v₀)| counts_eq_nil];
            [| now destruct counts]; simpl.
          rewrite c₀_to_v₀; simpl.

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
            (counts' & -> & _ & counts_eq_counts' & c₀_to_S_v₀ & H); simpl.
          constructor; change
              (Ok x₀ (max (S c₀) colors, Map.add p₀ c₀ labeling) counts').
          split_left.
                    assumption.
                  apply le_lt_or_eq in c₀_le_colors as
                    [c₀_lt_colors| ->].
                    rewrite max_r; [apply Coloring.Ok.add_lt|]...
                  rewrite max_l; [apply Coloring.Ok.add_eq|]...
                rewrite <- counts_eq_counts'.
                now apply Nat.max_lub.
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

              exists (add p₀ owners); split.
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
            unfold Count_Ok, ForNth in *.
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
          rewrite <- counts_eq_counts'.
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
  End Fixed.
End Make.

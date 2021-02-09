Set Implicit Arguments.

Require Import Coq.Structures.Equalities Coq.Structures.EqualitiesFacts.
Require Import Coq.Structures.Orders Coq.Structures.OrdersFacts.

Require Import Coq.Lists.List Coq.Lists.SetoidList.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Arith.Arith.

Require Coq.MSets.MSets.
Require Coq.FSets.FMaps.

Import ListNotations.

Require Import Shuffle.Misc.
Require Import Shuffle.List.
Require Shuffle.Assigned.Instructions.
Require Import Shuffle.Coloring.

Module Assigned (Owner : DecidableTypeBoth).
  Import Coq.FSets.FMaps.

  Module WFacts_fun' (Key : DecidableType) (Import Map : WSfun Key).
    Include WFacts_fun Key Map.

    Lemma find_spec : forall  [elt : Type] (m : Map.t elt) (x : Map.key),
      OptionSpec (fun e : elt => Map.MapsTo x e m) (~ Map.In x m) (Map.find x m).
    Proof.
      intros elt m x.
      destruct (find x m) eqn: find; constructor.
        now apply find_mapsto_iff.
      now apply not_find_in_iff.
    Qed.

    Lemma add_not_in_iff : forall [elt : Type] (m : Map.t elt) (x y : Map.key) (e : elt),
    ~ Map.In y (Map.add x e m) <-> ~ Key.eq x y /\ ~ Map.In y m.
    Proof.
      intros elt m x y e.
      rewrite add_in_iff; tauto.
    Qed.

    Lemma add_not_in : forall [elt : Type] (m : Map.t elt) (x y : Map.key) (e : elt),
      ~ Key.eq x y ->
      ~ Map.In y m ->
      ~ Map.In y (Map.add x e m).
    Proof.
      intros elt m x y e.
      rewrite add_in_iff; tauto.
    Qed.
  End WFacts_fun'.

  Section Subsets.
    Variables (A : Type) (P : list A -> Prop).

    Inductive Subsets  : list A -> Prop :=
    | Subsets_nil : P [] -> Subsets []
    | Subsets_cons : forall (u₀ : A) (x₀ : list A),
      P (u₀ :: x₀) -> Subsets x₀ -> Subsets (u₀ :: x₀).

    Lemma Subsets_inv : forall x : list A,
      Subsets x -> P x.
    Proof.
      intros x Subsets_x.
      now destruct Subsets_x as [P_x| u₀ x₀ P_x _].
    Qed.
  End Subsets.

  Module Regular (Map : WSfun Owner).
    Module Import Facts := WFacts_fun' Owner Map.

    Module Coloring := Coloring Owner Map.
    Module Import Instructions := Instructions.Make Owner.
    Import Instructions.Notations.

    Definition Color_Ok
      (instructions : list Instruction.t)
      (coloring : Coloring.t)
      (color : nat) :
      Prop :=
      (forall (owner : Owner.t) (n : nat),
        Active owner instructions ->
        Coloring.MapsTo coloring owner n ->
        color <> n) /\
      (exists owner : Owner.t,
        Coloring.MapsTo coloring owner color /\
        Absent owner instructions).

    Import Instructions.Ok.

    Fixpoint regular
      (instructions : list Instruction.t)
      (coloring : Coloring.t)
      (unused_colors : list nat) :
      option Coloring.t :=
      match instructions, unused_colors with
      | Up owner :: tail, [] => regular
        tail
        (Coloring.add_eq coloring owner)
        []
      | Up owner :: tail, color :: unused_colors => regular
        tail
        (Coloring.add_lt coloring owner color)
        unused_colors
      | Down owner :: tail, unused_colors =>
          bind (Coloring.find' coloring owner) (fun color =>
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

    Notation ActiveTo owner color coloring instructions :=
      (Active owner instructions /\ Coloring.MapsTo coloring owner color).

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

    Import Instructions.Hints.
    Ltac my_auto :=
      auto with relations instructions.

    Ltac Ok_intro :=
      intros
        (Ok_instructions &
        Ok_coloring &
        Synced_coloring &
        Proper_coloring &
        Ok_unused_colors &
        NoDup_unused_colors).

      Ltac Ok_destruct ok :=
        destruct ok as
          (Ok_instructions &
          Ok_coloring &
          Synced_coloring &
          Proper_coloring &
          Ok_unused_colors &
          NoDup_unused_colors).

    Definition Synced
      (instructions : list Instruction.t)
      (coloring : Coloring.t) :=
      forall owner : Owner.t,
        (Active owner instructions ->
        Coloring.Contains coloring owner) /\
        (Ahead owner instructions ->
        ~ Coloring.Contains coloring owner).

    Ltac split_left :=
      split; [| try split_left].

    Import Instructions.Ok.Hints.

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
          Ok_intro.
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
          unfold Coloring.MapsTo; simpl.
          rewrite ?add_mapsto_iff.
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
          Ok_intro.
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
            unfold Coloring.MapsTo; simpl.
            rewrite ?add_mapsto_iff.
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
            unfold Coloring.MapsTo; simpl.
            intros owner' n' Active_owner'.
            rewrite add_mapsto_iff.
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
        Coloring.Ok.t result /\
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
      destruct (Coloring.find' coloring owner) as [color|] eqn: find.
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
        Coloring.Ok.t result /\
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

  Module Fixed (Map : WSfun Owner).
    Module Import Facts := WFacts_fun' Owner Map.

    Module Coloring := Coloring Owner Map.
    Module Import Instructions := Instructions.Make Owner.
    Import Instructions.Notations.

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

    Import Instructions.Ok.

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
          bind (Coloring.find' coloring op₀) (fun color =>
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
      unfold Coloring.MapsTo.
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

    Ltac split_left :=
      split; [| try split_left].
    Ltac my_auto :=
      auto with relations instructions.
    Import Instructions.Hints.

    Module Assumptions.
      Definition Ok
        (instructions : Instructions.t)
        (coloring : Coloring.t)
        (counts : list nat) :
        Prop :=
        Instructions.Ok instructions /\
        Coloring.Ok coloring /\
        (Coloring.colors coloring <= length counts) /\ (* TODO *)
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
            bind (Coloring.find' coloring p₀) (fun color =>
            bind (nth_error counts color) (fun count =>
            replace counts color (pred count)))
          ).
      Proof with my_auto.
        intros p₀ x₀ coloring counts ok.
        Ok_destruct ok.
        unfold Coloring.find'; simpl.
        destruct (find_spec (Coloring.labeling coloring) p₀) as [c₀ p₀_to_c₀| not_In_p₀].
        2: {
          contradict not_In_p₀.
          apply Synced_coloring...
        }
        assert (c₀_lt_counts : c₀ < length counts).
          now apply lt_le_trans with (Coloring.colors coloring);
            [apply Ok_coloring; exists p₀|].
        simpl; specialize NthError.lt_Some with (1 := c₀_lt_counts) as (v₀ & c₀_to_v₀); rewrite c₀_to_v₀.
        simpl; specialize Replace.lt_Some with (v := pred v₀) (1 := c₀_lt_counts) as
          (counts' & -> & _ & counts_eq_counts' & c₀_to_pred & H).
        constructor; split_left.
                  now apply Instructions.Ok.cons_inv in Ok_instructions.
                assumption.
              now rewrite <- counts_eq_counts'.
            split; intros ?; apply Synced_coloring...
          intros n v' n_to_v'.
          assert (n_lt_counts : n < length counts).
            rewrite counts_eq_counts'.
            now apply NthError.Some_lt with v'.
          specialize NthError.lt_Some with (1 := n_lt_counts) as
            (v & n_to_v).
          unfold ForNth in Ok_counts.
          specialize Ok_counts with (1 := n_to_v) as
            (owners & owners_iff & owners_length).
          destruct (Nat.eq_dec n c₀) as [n_eq_c₀| n_neq_c₀].
            2: {
              exists owners.
              assert (Some v = Some v') as [= <-].
                rewrite <- n_to_v, <- n_to_v'.
                now apply H.
              split_left...
              intros p; split.
                intros In_p.
                apply owners_iff in In_p as (Active_p & p_to_color).
                split; [| assumption].
                apply Instructions.Active.cons_Down_inv with (1 := Active_p).
                apply StronglyExtensional with coloring c₀ n; [easy..|].
                now change (complement Logic.eq c₀ n); symmetry.
              intros (Active_p & p_to_n); apply owners_iff.
              split; [| assumption].
              now apply Instructions.Active.cons_Down.
            }
            exists (M.remove p₀ owners); split_left...
              intros p.
              rewrite M.remove_spec, owners_iff, n_eq_c₀, Instructions.Active.cons_Down_iff; [| assumption].
              assert (Owner.eq p₀ p <-> Owner.eq p p₀) as -> by easy.
              split; [tauto|].
              intros (Active_p & p_to_c₀).
              enough (~ Owner.eq p p₀) by tauto.
              enough (Absent p₀ x₀)...
            rewrite n_eq_c₀ in *.
            assert (S (cardinal (remove p₀ owners)) = cardinal owners).
              apply remove_cardinal_1, owners_iff...
            assert (Some v = Some v₀) as [= ->] by
              now transitivity (nth_error counts c₀).
            assert (Some v' = Some (pred v₀)) as [= ->] by
              now transitivity (nth_error counts' c₀).
            rewrite <- owners_length.
            change (pred (S (cardinal (remove p₀ owners))) = pred (cardinal owners)).
            now f_equal.
          intros c (colors_le_c & c_lt_counts').
          rewrite <- (H c).
            now apply Ok_zero; rewrite counts_eq_counts'.
          change (complement Logic.eq c c₀); symmetry.
          now apply Nat.lt_neq, lt_le_trans with (Coloring.colors coloring);
            [apply Ok_coloring; exists p₀|].
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
          destruct (Min'.minimum_spec counts) as [[c v] Min_v| counts_eq_nil];
            [| now destruct counts]; simpl.
          set (colors := Coloring.colors coloring).
          destruct Min_v as (Min_v & c_to_v).
          assert (c_lt_counts : c < length counts) by
            now apply NthError.Some_lt with v.
          assert (c_le_colors : c <= colors).
            apply not_gt.
            specialize Nat.nlt_0_r with v as c_gt_colors; contradict c_gt_colors.
            assert (colors_to_0 : Nth counts colors O)  by
              now apply Ok_zero; split; [| transitivity c].
            now apply Min_v with (1 := colors_to_0).
          assert (not_In_p₀ : ~ Coloring.Contains coloring p₀).
            apply Synced_coloring...
          assert (max_r : c < colors -> Init.Nat.max (S c) colors = colors).
            now intros c_lt_colors; apply Nat.max_r.
          assert (max_l : c = colors -> Init.Nat.max (S c) colors = S colors).
            now intros ->; apply Nat.max_l, Nat.le_succ_diag_r.
          rewrite c_to_v; simpl.
          specialize Replace.lt_Some with (v := S v) (1 := c_lt_counts) as
            (counts' & -> & Ok_counts').
          destruct Ok_counts' as (_ & counts_eq_counts' & c_to_S_v & H).
          simpl.
          constructor; change
              (Ok x₀ (max (S c) colors, Map.add p₀ c (Coloring.labeling coloring)) counts').
          split_left.
                    now inversion Ok_instructions.
                  apply le_lt_or_eq in c_le_colors as
                    [c_lt_colors| c_eq_colors].
                    rewrite max_r by assumption.
                    apply Coloring.Ok.add_lt...
                  rewrite max_l, c_eq_colors by assumption.
                  apply Coloring.Ok.add_eq...
                rewrite <- counts_eq_counts'.
                now apply Nat.max_lub.
              intros p; split.
                intros Active_x₀; apply add_in_iff.
                destruct (Owner.eq_dec p₀ p) as [p₀_eq_p| p₀_neq_p];
                  [left| right; apply Synced_coloring]...
              intros Ahead_p.
              apply add_not_in_iff; split...
                enough (Active p₀ x₀)...
              apply Synced_coloring...
            intros c' v' c'_to_v'.
            destruct (Nat.eq_dec c' c) as [c'_eq_c| c'_neq_c].
              rewrite c'_eq_c in *.
              unfold ForNth in Ok_counts.
              specialize Ok_counts with (1 := c_to_v) as
              (owners & owners_iff & owners_length).
              exists (add p₀ owners).
              split.
                intro p.
                rewrite add_iff, owners_iff.
                split.
                  unfold Coloring.MapsTo; simpl.
                  intros [<-| (Active_p & p_to_c)].
                    split.
                      now apply Instructions.Ok.cons_Up_inv in Ok_instructions.
                    now apply Map.add_1.
                  assert (~ Owner.eq p₀ p).
                    enough (Ahead p₀ (Up p₀ :: x₀))...
                  split.
                    now apply Instructions.Active.cons_Up_inv with p₀.
                  now apply Map.add_2.
                unfold Coloring.MapsTo; simpl.
                intros (Active_p & p_to_c).
                apply add_mapsto_iff in p_to_c as [(p₀_eq_p & _)| (p₀_neq_p & p_to_c)]; [now left| right].
                split...
              rewrite add_cardinal_2.
              rewrite owners_length.
              enough (Some (S v) = Some v') as [=] by easy.
                now transitivity (nth_error counts' c).
              intros In_p₀.
              apply owners_iff in In_p₀ as (Active_p₀ & _).
              enough (~ Owner.eq p₀ p₀) by auto.
              enough (Ahead p₀ (Up p₀ :: x₀))...
            rewrite <- H in c'_to_v' by assumption.
            unfold ForNth in Ok_counts.
            specialize Ok_counts with (1 := c'_to_v') as
              (owners & owners_iff & owners_length).
            exists owners; split; [| assumption].
            unfold Coloring.MapsTo; simpl.
            intros p.
            rewrite owners_iff.
            split; intros (Active_p & p_to_c').
              split.
                now apply Instructions.Active.cons_Up_inv with p₀.
              apply Map.add_2; [enough (Ahead p₀ (Up p₀ :: x₀))|]...
            apply add_mapsto_iff in p_to_c' as [(_ & c_eq_c')| (p₀_neq_p & p_to_c')]; [now contradict c'_neq_c|].
            split...
          rewrite <- counts_eq_counts'.
          intros c' (colors'_le_c & c_lt_counts').
          apply le_lt_or_eq in c_le_colors as
            [c_lt_colors| c_eq_colors].
            rewrite max_r in colors'_le_c by assumption; simpl in colors'_le_c.
            rewrite <- (H c').
              now apply Ok_zero.
            enough (c <> c') by auto with arith.
            now apply Nat.lt_neq, lt_le_trans with colors.
          rewrite max_l in colors'_le_c by assumption; simpl in colors'_le_c.
          rewrite <- (H c').
            apply Ok_zero; auto with arith.
          rewrite c_eq_colors.
          enough (colors <> c') by auto with arith.
          now apply Nat.lt_neq.
        Qed.
    End Assumptions.
  End Fixed.
End Assigned.

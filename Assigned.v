Set Implicit Arguments.

Require Import Coq.Structures.Equalities Coq.Structures.EqualitiesFacts.
Require Import Coq.Structures.Orders Coq.Structures.OrdersFacts.

Require Import Coq.Lists.List Coq.Lists.SetoidList.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Arith.Arith.

Require Coq.FSets.FMaps.

Import ListNotations.

Require Import Shuffle.Misc.
Require Import Shuffle.List.
Require Import Shuffle.Instruction.
Require Import Shuffle.Coloring.

Module Opcode <: UsualDecidableType.
  Inductive Opcode : Set :=
  | Up : Opcode
  | Down : Opcode.

  Definition t : Type := Opcode.

  Include HasUsualEq.
  Include UsualIsEq.

  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
  Proof.
    decide equality.
  Qed.

  Lemma not_Up_iff_Down : forall opcode : t, Up <> opcode <-> Down = opcode.
  Proof.
    now intros [|].
  Defined.

  Lemma not_Down_iff_Up : forall opcode : t, Down <> opcode <-> Up = opcode.
  Proof.
    now intros [|].
  Defined.
End Opcode.

Section InA.
  Variables
    (A : Type)
    (eqA : A -> A -> Prop)
    (u v₀ : A)
    (y₀ y : list A).

  Lemma not_InA_cons :
    ~ InA eqA u (v₀ :: y₀) <->
    ~ eqA u v₀ /\ ~ InA eqA u y₀.
  Proof.
    rewrite InA_cons; firstorder.
  Qed.

  Lemma not_InA_iff :
  ~ InA eqA u y <->
  Forall (fun v => ~ eqA u v) y.
  Proof.
    now rewrite InA_altdef, <- Forall_Exists_neg.
  Qed.
End InA.

Lemma Forall_cons_iff : forall
  (A : Type)
  (P : A -> Prop)
  (u₀ : A)
  (x₀ : list A),
  Forall P (u₀ :: x₀) <->
    P u₀ /\ Forall P x₀.
Proof.
  intros A P u₀ x₀.
  split.
    intros Forall_x.
    constructor.
      now apply Forall_inv with x₀.
    now apply Forall_inv_tail with u₀.
  intros [P_u₀ Forall_x₀].
  now constructor.
Qed.

Local Lemma not_In_Forall : forall
  (A : Type)
  (u : A)
  (y : list A),
  ~ List.In u y <-> Forall (fun v => u <> v) y.
Proof.
  induction y as [| v₀ y₀ IHy₀].
    easy.
  rewrite Forall_cons_iff, not_in_cons; firstorder.
Qed.

Module Assigned (Owner : DecidableTypeBoth).
  Module Instruction := Instruction Opcode Owner.

  Module Instructions.
    Definition t : Type :=
      list Instruction.t.

    Module Notations.
      Notation Up owner :=
        ((Opcode.Up, owner)).

      Notation Down owner :=
        ((Opcode.Down, owner)).

      Notation In instruction instructions :=
        (InA Instruction.eq instruction instructions).

      Notation Ahead owner instructions :=
        (In (Up owner) instructions).

      Notation Active owner instructions :=
        (~ In (Up owner) instructions /\
        In (Down owner) instructions).

      Notation Absent owner instructions :=
        (~ In (Down owner) instructions).
    End Notations.
    Import Notations.

    Inductive Ok : list Instruction.t -> Prop :=
    | nil : Ok []
    | cons_Up : forall (op₀ : Owner.t) (x₀ : list Instruction.t),
      Active op₀ x₀ ->
      Ok x₀ ->
      Ok (Up op₀ :: x₀)
    | cons_Down : forall (op₀ : Owner.t) (x₀ : list Instruction.t),
      Absent op₀ x₀ ->
      Ok x₀ ->
      Ok (Down op₀ :: x₀).

    Module Orthogonal.
      Section Orthogonal.
        Variables
          (v w : Owner.t)
          (x : t).

        Lemma Up_impl_Down :
          Ok x ->
          Ahead v x ->
          In (Down v) x.
        Proof.
          intros Ok_x.
          induction Ok_x as [| op₀ x₀ Active_op₀ Ok_x₀ IHx₀| op₀ x₀ Absent_op₀ Ok_x₀ IHx₀];
            intros Ahead_v; [easy| ..].
            1 - 2:
            apply InA_cons in Ahead_v as [(eq & v_eq_op₀)| Ahead_v];
            [change (Owner.eq v op₀) in v_eq_op₀| now right; apply IHx₀].
              now rewrite v_eq_op₀; right.
            now contradict eq; apply Opcode.not_Up_iff_Down.
        Qed.

        Lemma Ahead_Active :
          Ahead v x ->
          Active w x ->
          ~ Owner.eq v w.
        Proof.
          intros Ahead_v Active_w v_eq_w.
          now rewrite v_eq_w in Ahead_v.
        Qed.

        Lemma Active_Absent :
          Active v x ->
          Absent w x ->
          ~ Owner.eq v w.
        Proof.
          intros Active_v Absent_w v_eq_w.
          now rewrite v_eq_w in Active_v.
        Qed.

        Lemma Ahead_Absent :
          Ok x ->
          Ahead v x ->
          Absent w x ->
          ~ Owner.eq v w.
        Proof.
          intros Ok_x Ahead_v Absent_v.
          contradict Absent_v; rewrite <- Absent_v.
          now apply Up_impl_Down.
        Qed.
      End Orthogonal.

      Module Hints.
        Ltac solve_neq :=
          match goal with
          | |- ~ Owner.eq ?v ?w => change(complement Owner.eq v w)
          end;
          (idtac + symmetry);
          match goal with
          | |- complement Owner.eq ?v ?w =>
            match goal with
            | _ : Ahead v ?x, _ : Active w ?x |- _ =>
              now apply Orthogonal.Ahead_Active with x
            | _ : Ahead v ?x, _ : Absent w ?x |- _ =>
              now apply Orthogonal.Ahead_Absent with x
            | _ : Active v ?x, _ : Absent w ?x |- _ =>
              now apply Orthogonal.Active_Absent with x
            end
          end.

        #[export]
        Hint Extern 2 (~ (Owner.eq _ _)) => solve_neq : instructions.
      End Hints.
    End Orthogonal.

    Module Ok.
      Section Ok.
        Variables
          (op₀ v : Owner.t)
          (u₀ : Instruction.t)
          (x₀ x : t).

        Lemma cons_inv :
          Ok (u₀ :: x₀) ->
          Ok x₀.
        Proof.
          now inversion 1.
        Qed.

        Lemma cons_Up_inv :
          Ok (Up op₀ :: x₀) ->
          Active op₀ x₀.
        Proof.
          intros Ok_x₀.
          now inversion_clear Ok_x₀.
        Qed.

        Lemma cons_Down_inv :
          Ok (Down op₀ :: x₀) ->
          Absent op₀ x₀.
        Proof.
          intros Ok_x₀.
          now inversion_clear Ok_x₀.
        Qed.

        Lemma cons_Up_iff : (* TODO *)
          Ok (Up op₀ :: x₀) <->
            Active op₀ x₀ /\
            Ok x₀.
        Proof.
          now split; [inversion_clear 1| constructor].
        Qed.

        Lemma cons_Down_iff :
          Ok (Down op₀ :: x₀) <->
            Absent op₀ x₀ /\
            Ok x₀.
        Proof.
          now split; [inversion_clear 1| constructor].
        Qed.
      End Ok.

      Module Hints.
        #[export]
        Hint Constructors Ok : instructions.
        #[export]
        Hint Immediate cons_Up_inv : instructions.
        #[export]
        Hint Immediate cons_Down_inv : instructions.
      End Hints.
    End Ok.

    Module Ahead.
      Section Ahead.
        Variables
          (op₀ v : Owner.t)
          (u₀ : Instruction.t)
          (x₀ : t).

        Lemma cons :
          Ahead v x₀ ->
          Ahead v (u₀ :: x₀).
        Proof.
          now right.
        Qed.

        Lemma cons_Up :
          Owner.eq op₀ v ->
          Ahead v (Up op₀ :: x₀).
        Proof.
          now intros op₀_eq_v; left.
        Qed.

        Lemma nil_inv : ~ Ahead v [].
        Proof.
          intros Ahead_v.
          apply InA_nil with (1 := Ahead_v).
        Qed.

        Lemma cons_Up_inv :
          Ahead v (Up op₀ :: x₀) ->
          ~ Owner.eq op₀ v ->
          Ahead v x₀.
        Proof.
          intros Ahead_v op₀_neq_v.
          now apply InA_cons in Ahead_v as [(_ & op₀_eq_v)| Ahead_v];
            [absurd (Owner.eq op₀ v)|].
        Qed.

        Lemma cons_Down_inv :
          Ahead v (Down op₀ :: x₀) ->
          Ahead v x₀.
        Proof.
          intros Ahead_v.
          now apply InA_cons in Ahead_v as [(Up_eq_Down & _)| Ahead_v];
            [contradict Up_eq_Down; apply Opcode.not_Up_iff_Down|].
        Qed.

        Lemma nil_iff :
          Ahead v [] <-> False.
        Proof.
          now split; [apply nil_inv|].
        Qed.

        Lemma cons_Up_iff :
          Ahead v (Up op₀ :: x₀) <->
            Owner.eq op₀ v \/ Ahead v x₀.
        Proof.
          split.
            now destruct (Owner.eq_dec op₀ v) as [op₀_eq_v| op₀_neq_v];
              [left| right; apply cons_Up_inv].
          now intros [op₀_eq_v| Ahead_v]; [left| right].
        Qed.

        Lemma cons_Down_iff :
          Ahead v (Down op₀ :: x₀) <->
          Ahead v x₀.
        Proof.
          now split; [apply cons_Down_inv| right].
        Qed.
      End Ahead.

      Module Hints.
        #[export]
        Hint Resolve cons : instructions.
        #[export]
        Hint Resolve cons_Up : instructions.

        #[export]
        Hint Immediate nil_inv : instructions.
      End Hints.
    End Ahead.

    Module Active.
      Section Active.
        Variables
          (op₀ v : Owner.t)
          (x₀ : t).

        Lemma cons_Up :
          ~ Owner.eq op₀ v ->
          Active v x₀ ->
          Active v (Up op₀ :: x₀).
        Proof.
          intros op₀_neq_v Active_v.
          split; [| now right].
          now apply not_InA_cons; split;
            [apply Instruction.neq_operand; contradict op₀_neq_v|].
        Qed.

        Lemma cons_Down :
          Active v x₀ ->
          Active v (Down op₀ :: x₀).
        Proof.
          intros Active_v.
          split; [| now right].
          now apply not_InA_cons; split;
            [apply Instruction.neq_opcode, Opcode.not_Up_iff_Down|].
        Qed.

        Lemma cons_Down_eq :
          Ok (Down op₀ :: x₀) ->
          Owner.eq op₀ v ->
          Active v (Down op₀ :: x₀).
        Proof.
          intros Ok_instructions op₀_eq_v.
          apply Ok.cons_Down_iff in Ok_instructions as (Absent_op₀ & Ok_instructions).
          split; [| now left].
          contradict op₀_eq_v; apply Ahead.cons_Down_inv in op₀_eq_v.
          Orthogonal.Hints.solve_neq.
        Qed.

        Lemma nil_inv : ~ Active v [].
        Proof.
          intros (_ & In_Down_v).
          apply InA_nil with (1 := In_Down_v).
        Qed.

        Lemma cons_Up_inv :
          Active v (Up op₀ :: x₀) ->
          Active v x₀.
        Proof.
          intros (not_Ahead_v & In_Down_v).
          split.
            now contradict not_Ahead_v; right.
          now apply InA_cons in In_Down_v as [(Down_eq_Up & _)| In_Down_v];
            [contradict Down_eq_Up; apply Opcode.not_Down_iff_Up|].
        Qed.

        Lemma cons_Down_inv :
          Active v (Down op₀ :: x₀) ->
          ~ Owner.eq op₀ v ->
          Active v x₀.
        Proof.
          intros (not_Ahead_v & In_Down_v) op₀_neq_v.
          split.
            now contradict not_Ahead_v; right.
          now apply InA_cons in In_Down_v as [(_ & v_eq_op₀)| In_Down_v];
            [absurd (Owner.eq op₀ v)|].
        Qed.

        Lemma nil_iff : Active v [] <-> False.
        Proof.
          now split; [apply nil_inv|].
        Qed.

        Lemma cons_Up_iff :
          Active v (Up op₀ :: x₀) <->
            ~ Owner.eq op₀ v /\ Active v x₀.
        Proof.
          split.
            intros Active_v; split.
              assert (Ahead_op₀ : Ahead op₀ (Up op₀ :: x₀)) by now left.
              Orthogonal.Hints.solve_neq.
            now apply cons_Up_inv.
          now intros (op₀_eq_v & Active_v); apply cons_Up.
        Qed.

        Lemma cons_Down_iff :
          Ok (Down op₀ :: x₀) ->
            Active v (Down op₀ :: x₀) <->
              Owner.eq op₀ v \/ Active v x₀.
        Proof.
          intros Ok_instructions.
          split.
            destruct (Owner.eq_dec op₀ v) as [op₀_eq_v| op₀_neq_v];
              [now left| right].
            now apply cons_Down_inv.
          now intros [op₀_eq_v| Active_v];
            [apply cons_Down_eq| apply cons_Down].
        Qed.
      End Active.

      Module Hints.
        #[export]
        Hint Resolve cons_Up :  instructions.
        #[export]
        Hint Resolve cons_Down :  instructions.
        #[export]
        Hint Resolve cons_Down_eq :  instructions.

        #[export]
        Hint Immediate nil_inv : instructions.
      End Hints.
    End Active.

    Module Absent.
      Section Absent.
        Variables
          (op₀ v : Owner.t)
          (u₀ : Instruction.t)
          (x₀ : t).

        Lemma nil : Absent v [].
        Proof.
          unfold not; apply InA_nil.
        Qed.

        Lemma cons_Up :
          Absent v x₀ ->
          Absent v (Up op₀ :: x₀).
        Proof.
          intros Absent_v.
          now apply not_InA_cons; split;
            [apply Instruction.neq_opcode, Opcode.not_Down_iff_Up|].
        Qed.

        Lemma cons_Down :
          ~ Owner.eq op₀ v ->
          Absent v x₀ ->
          Absent v (Down op₀ :: x₀).
        Proof.
          intros op₀_neq_v Absent_v.
          now apply not_InA_cons; split;
            [apply Instruction.neq_operand; contradict op₀_neq_v|].
        Qed.

        Lemma cons_inv :
          Absent v (u₀ :: x₀) ->
          Absent v x₀.
        Proof.
          intros Absent_v.
          now apply not_InA_cons in Absent_v.
        Qed.

        Lemma nil_iff : Absent v [] <-> True.
        Proof.
          easy.
        Qed.

        Lemma cons_Down_iff :
          Absent v (Down op₀ :: x₀) <->
            ~ Owner.eq op₀ v /\ Absent v x₀.
        Proof.
          split; intros Absent_v; [| now apply cons_Down].
          apply not_InA_cons in Absent_v as (v_neq_op₀ & Absent_v).
          apply Instruction.neq_eq_opcode in v_neq_op₀; [| reflexivity].
          now split; [contradict v_neq_op₀|].
        Qed.
      End Absent.

      Lemma cons_Up_iff : forall op₀ v x₀,
        Absent v (Up op₀ :: x₀) <->
        Absent v x₀.
      Proof.
        split.
          apply cons_inv.
        now intros Absent_v; apply not_InA_cons; split;
          [apply Instruction.neq_opcode, Opcode.not_Down_iff_Up|].
      Qed.

      Module Hints.
        #[export]
        Hint Resolve nil : instructions.
        #[export]
        Hint Resolve cons_Up : instructions.
        #[export]
        Hint Resolve cons_Down : instructions.
      End Hints.
    End Absent.

    Module Hints.
      Create HintDb instructions.

      Export Ok.Hints.
      Export Orthogonal.Hints.
      Export Ahead.Hints.
      Export Active.Hints.
      Export Absent.Hints.
    End Hints.
  End Instructions.

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

    Module IgnoreIndex (Index : Typ) (Import Data : Ord) <: Ord.
      Definition t : Type :=
        Index.t * Data.t.
      
      Definition index (self : t) : Index.t :=
        fst self.
      Definition data (self : t) : Data.t :=
        snd self.

      Definition eq (self other : t) : Prop :=
        data self == data other.
      Definition lt (self other : t) : Prop :=
        data self < data other.
      Definition le (self other : t) : Prop :=
        data self <= data other.

      Include EqLtLeNotation.

      Definition eqb (self other : t) : bool :=
        data self =? data other.
      Definition ltb (self other : t) : bool :=
        data self <? data other.
      Definition leb (self other : t) : bool :=
        data self <=? data other.

      Include EqbNotation <+ LtbNotation <+ LebNotation.

      Definition compare (self other : t) : comparison :=
        data self ?= data other.

      Include CmpNotation.

      Instance eq_equiv : Equivalence eq.
      Proof.
        unfold eq.
        split.
            intros x.
            reflexivity.
          intros x y x_eq_y.
          now symmetry.
        intros x y z x_eq_y y_eq_z.
        now transitivity (data y).
      Qed.

      Section CompareBasedOrder.
        Variables x y : t.

        Lemma compare_eq_iff : (x ?= y) = Eq <-> x == y.
        Proof.
          apply Data.compare_eq_iff.
        Qed.

        Lemma compare_lt_iff : (x ?= y) = Lt <-> x < y.
        Proof.
          apply Data.compare_lt_iff.
        Qed.

        Lemma compare_le_iff : (x ?= y) <> Gt <-> x <= y.
        Proof.
          apply Data.compare_le_iff.
        Qed.

        Lemma compare_antisym : (y ?= x) = CompOpp (x ?= y).
        Proof.
          apply Data.compare_antisym.
        Qed.
      End CompareBasedOrder.

      Section BoolOrdSpecs.
        Variables x y : t.

        Lemma eqb_eq : x =? y = true <-> x == y.
        Proof.
          apply Data.eqb_eq.
        Qed.

        Lemma ltb_lt : x <? y = true <-> x < y.
        Proof.
          apply Data.ltb_lt.
        Qed.

        Lemma leb_le : x <=? y = true <-> x <= y.
        Proof.
          apply Data.leb_le.
        Qed.
      End BoolOrdSpecs.

      Instance lt_strorder : StrictOrder lt.
      Proof.
        split.
          intros x.
          exact (irreflexivity (x := data x)).
        intros x y z x_lt_y y_lt_z.
        exact (transitivity (A := Data.t) x_lt_y y_lt_z).
      Qed.

      Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
      Proof.
        intros x x' x_eq_x' y y' y_eq_y';
        now apply Data.lt_compat.
      Qed.
    End IgnoreIndex.

    Module Min (Import O : Ord).
      Module Import Facts := OrdFacts O.

      Definition Min (v : t) (x : list t) :=
        List.In v x /\ Forall (fun u => v <= u) x.

      Fixpoint minimum_body
        (v : t)
        (x : list t) :
        t :=
        match x with
        | [] => v
        | u₀ :: x₀ =>
          if u₀ <? v then
            minimum_body u₀ x₀
          else
            minimum_body v x₀
        end.

      Definition minimum
        (x : list t) :
        option t :=
        match x with
        | [] => None
        | u₀ :: x₀ => Some (minimum_body u₀ x₀)
        end.

      Lemma minimum_body_Forall_le : forall (x : list t) (v : t),
        minimum_body v x <= v /\
        Forall (fun u => minimum_body v x <= u) x.
      Proof.
        induction x as [| u₀ x₀ IHx₀]; intros v; split.
              reflexivity.
            constructor.
          simpl; destruct (ltb_spec u₀ v) as [u₀_lt_v| u₀_ge_v].
            now transitivity u₀;
              [apply IHx₀| apply le_lteq; left].
            apply IHx₀.
        simpl; destruct (ltb_spec u₀ v); constructor;
          [..|transitivity v; [| assumption]|]; apply IHx₀.
      Qed.

      Lemma minimum_body_In : forall (x : list t) (v : t),
        minimum_body v x = v \/
        List.In (minimum_body v x) x.
      Proof.
        induction x as [| u₀ x₀ IHx₀]; intros v.
          now left.
        simpl; destruct (ltb_spec u₀ v) as [u₀_lt_v| u₀_ge_v].
          now specialize IHx₀ with u₀ as [|];
            right; [left| right].
        now specialize IHx₀ with v as [|];
          [left| right; right].
      Qed.

      Lemma minimum_spec : forall x : list t,
        OptionSpec (fun v => Min v x) (x = []) (minimum x).
      Proof.
        destruct x as [| u₀ x₀]; constructor.
          reflexivity.
        split.
          now specialize minimum_body_In with x₀ u₀ as [|];
            [left| right].
        constructor; apply minimum_body_Forall_le.
      Qed.
    End Min.
  End Fixed.
End Assigned.

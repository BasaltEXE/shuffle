Set Implicit Arguments.

Require Import Coq.Structures.Equalities Coq.Structures.EqualitiesFacts.
Require Import Coq.Lists.List Coq.Lists.SetoidList.

Require Import Coq.Program.Program.

Require Coq.FSets.FMaps.

Import ListNotations.

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

Section Option.
  Variable (A B : Type).

  Definition bind (mx : option A) (f : A -> option B) : option B :=
    match mx with
    | Some x => f x
    | None => None
    end.
  Definition then' (mx : option A) (my : option B) : option B :=
      bind mx (fun _ => my).
  Definition ret (a : A) : option A :=
    Some a.
End Option.

Module Assigned (Owner : DecidableType).
  Module Instruction := Instruction Opcode Owner.

  Lemma not_InA_cons : forall (A : Type) (eqA : A -> A -> Prop) (u v₀ : A) (y₀ : list A),
    ~ InA eqA u (v₀ :: y₀) <->
    ~ eqA u v₀ /\ ~ InA eqA u y₀.
  Proof.
    intros A eqA u v₀ y₀.
    rewrite InA_cons; firstorder.
  Qed.

  Module Ok.
    Notation add_Up owner instructions :=
      ((Opcode.Up, owner) :: instructions).

    Notation add_Down owner instructions :=
      ((Opcode.Down, owner) :: instructions).

    Definition InUp (owner : Owner.t) (instructions : list Instruction.t) : Prop :=
      InA Instruction.eq (Opcode.Up, owner) instructions.

    Definition InDown (owner : Owner.t) (instructions : list Instruction.t) : Prop :=
      InA Instruction.eq (Opcode.Down, owner) instructions.

    Ltac In_aux :=
      unfold InUp, InDown; 
      rewrite InA_cons;
      firstorder using Opcode.not_Up_iff_Down.

    Lemma InUp_add_Up
      (owner owner' : Owner.t)
      (instructions : list Instruction.t) :
      InUp owner (add_Up owner' instructions) <->
      Owner.eq owner owner' \/ InUp owner instructions.
    Proof.
      In_aux.
    Qed.

    Lemma InUp_add_Down
      (owner owner' : Owner.t)
      (instructions : list Instruction.t) :
      InUp owner (add_Down owner' instructions) <->
      InUp owner instructions.
    Proof.
      In_aux.
    Qed.

    Lemma InDown_add_Up
      (owner owner' : Owner.t)
      (instructions : list Instruction.t) :
      InDown owner (add_Up owner' instructions) <->
      InDown owner instructions.
    Proof.
      In_aux.
    Qed.

    Lemma InDown_add_Down
      (owner owner' : Owner.t)
      (instructions : list Instruction.t) :
      InDown owner (add_Down owner' instructions) <->
      Owner.eq owner owner' \/ InDown owner instructions.
    Proof.
      In_aux.
    Qed.

    Lemma not_InUp_add_Up
      (owner owner' : Owner.t)
      (instructions : list Instruction.t) :
      ~ InUp owner (add_Up owner' instructions) <->
      ~ Owner.eq owner owner' /\ ~ InUp owner instructions.
    Proof.
      firstorder using InUp_add_Up.
    Qed.

    Lemma not_InUp_add_Down
      (owner owner' : Owner.t)
      (instructions : list Instruction.t) :
      ~ InUp owner (add_Down owner' instructions) <->
      ~ InUp owner instructions.
    Proof.
      firstorder using InUp_add_Down.
    Qed.

    Lemma not_InDown_add_Up
      (owner owner' : Owner.t)
      (instructions : list Instruction.t) :
      ~ InDown owner (add_Up owner' instructions) <->
      ~ InDown owner instructions.
    Proof.
      firstorder using InDown_add_Up.
    Qed.

    Lemma not_InDown_add_Down
      (owner owner' : Owner.t)
      (instructions : list Instruction.t) :
      ~ InDown owner (add_Down owner' instructions) <->
      ~ Owner.eq owner owner' /\ ~ InDown owner instructions.
    Proof.
      firstorder using InDown_add_Down.
    Qed.

    Definition Active (owner : Owner.t) (instructions : list Instruction.t) : Prop :=
      ~ InUp owner instructions /\
      InDown owner instructions.

    Inductive Ok : list Instruction.t -> Prop :=
    | nil : Ok []
    | cons_Up : forall (owner : Owner.t) (tail : list Instruction.t),
      Ok tail ->
      Active owner tail ->
      Ok ((Opcode.Up, owner) :: tail)
    | cons_Down : forall (owner : Owner.t) (tail : list Instruction.t),
      Ok tail ->
      ~ InDown owner tail -> 
      Ok ((Opcode.Down, owner) :: tail).

    Lemma cons_Up_iff : forall (owner : Owner.t) (tail : list Instruction.t), 
      Ok ((Opcode.Up, owner) :: tail) <->
        Active owner tail /\
        Ok tail.
    Proof.
      intros.
      now split; [inversion_clear 1| constructor].
    Qed.

    Lemma cons_Down_iff : forall (owner : Owner.t) (tail : list Instruction.t),
      Ok ((Opcode.Down, owner) :: tail) <->
        ~ InDown owner tail /\
        Ok tail.
    Proof.
      intros.
      split.
        now inversion_clear 1.
      now constructor.
    Qed.

    Lemma InUp_impl_InDown : forall (owner : Owner.t) (instructions : list Instruction.t),
      Ok instructions ->
      InUp owner instructions ->
      InDown owner instructions.
    Proof.
      intros owner instructions Ok_instructions.
      induction Ok_instructions as [| owner' tail Ok_tail IHtail [not_In_Up not_In_Down]| owner' tail Ok_tail IHtail not_In_Down]; intros In_Up.
          now apply InA_nil in In_Up.
        constructor 2.
        apply InA_cons in In_Up as [[_ owner_eq_owner']| In_Up].
          change (Owner.eq owner owner') in owner_eq_owner'.
          now rewrite owner_eq_owner'.
        now apply IHtail.
      apply InA_cons in In_Up as [[Up_eq_Down _]| In_Up].
        change (Opcode.Up = Opcode.Down) in Up_eq_Down.
        discriminate Up_eq_Down.
      constructor 2.
      now apply IHtail.
    Qed.

    Lemma not_InDown_impl_not_InUp : forall (owner : Owner.t) (instructions : list Instruction.t),
      Ok instructions ->
      ~ InDown owner instructions ->
      ~ InUp owner instructions.
    Proof.
      firstorder using InUp_impl_InDown.
    Qed.

    Lemma Active_nil (owner : Owner.t) : ~ Active owner [].
    Proof.
      intros [not_InUp_owner InDown_owner].
      apply InA_nil with (1 := InDown_owner).
    Qed.

    Lemma Active_cons_Up (owner owner' : Owner.t) (instructions : list Instruction.t) :
      Active owner ((Opcode.Up, owner') :: instructions) <->
        ~ Owner.eq owner owner' /\ Active owner instructions.
    Proof.
      unfold Active, InUp, InDown.
      rewrite not_InA_cons, InA_cons, Instruction.neq_eq_opcode by reflexivity; simpl.
      firstorder.
    Qed.

    Lemma Active_cons_Down (owner owner' : Owner.t) (instructions : list Instruction.t) :
      Ok ((Opcode.Down, owner') :: instructions) ->
      Active owner ((Opcode.Down, owner') :: instructions) <->
      Owner.eq owner owner' \/ Active owner instructions.
    Proof.
      intros Ok_instructions.
      unfold Active, InUp, InDown.
      rewrite not_InA_cons, InA_cons.
      apply cons_Down_iff in Ok_instructions as [not_InDown_owner' Ok_instructions].
      split.
        intros ((_ & not_InUp_owner) & [(_ & owner_eq_owner')| InDown_owner]); [now left| right].
        now split.
      intros [owner_eq_owner'| (not_InDown_owner & InDown_owner)].
        firstorder.
          now apply Instruction.neq_opcode, Opcode.not_Up_iff_Down.
        rewrite owner_eq_owner'.
        now apply not_InDown_impl_not_InUp.
      firstorder.
      now apply Instruction.neq_opcode.
    Qed.

    Lemma InUp_Active (owner owner' : Owner.t) (instructions : list Instruction.t) :
      Active owner instructions ->
      InUp owner' instructions ->
      ~ Owner.eq owner owner'. (* TODO *)
    Proof.
        intros (not_InUp_owner & _) InUp_owner' owner_eq_owner'.
        unfold InUp in *. (* TODO *)
        now rewrite <- owner_eq_owner' in InUp_owner'.
    Qed.

    Lemma not_InDown_Active (owner owner' : Owner.t) (instructions : list Instruction.t) :
      Active owner instructions ->
      ~ InDown owner' instructions ->
      ~ Owner.eq owner owner'. (* TODO *)
    Proof.
        intros (not_InUp_owner & InDown_owner) not_InDown_owner' owner_eq_owner'.
        unfold InDown in *. (* TODO *)
        now rewrite <- owner_eq_owner' in not_InDown_owner'.
    Qed.
  End Ok.
(* 
  Definition Rel : relation Instruction.t :=
    fun self other =>
    Owner.eq (Instruction.operand self) (Instruction.operand other) ->
      Instruction.opcode self = Opcode.Up /\
      Instruction.opcode other = Opcode.Down.

  Definition Ok : list Instruction.t -> Prop :=
    fun instructions => 
    ForallOrdPairs Rel instructions /\ (forall owner : Owner.t, InA Instruction.eq (Opcode.Up, owner) instructions -> InA Instruction.eq (Opcode.Down, owner) instructions).

  Definition Forall_iff : forall (A : Type) (P : A -> Prop) (u₀ : A) (x₀ : list A), Forall P (u₀ :: x₀) <-> P u₀ /\ Forall P x₀.
  Proof.
    intros A P u₀ x₀.
    split.
      intros Forall_x.
      constructor.
        now apply Forall_inv with x₀.
      now apply Forall_inv_tail with u₀.
    intros [P_u₀ Forall_x₀].
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

  Lemma not_InA_iff : forall (A : Type) (eqA : A -> A -> Prop) (u : A) (y : list A), ~ InA eqA u y <-> Forall (fun v => ~ eqA u v) y.
  Proof.
    intros A eqA u y.
    now rewrite InA_altdef, <- Forall_Exists_neg.
  Qed.

  Instance Instruction_Rel_Proper : forall instruction : Instruction.t, Proper (Instruction.eq ==> iff) ( Rel instruction).
  Proof.
    intros [opcode₁ owner₁] [opcode₂ owner₂] [opcode₃ owner₃] [H₁ H₂].
    simpl in *.
    simpl in *.
    unfold Rel.
    compute in *.
    now rewrite H₁, H₂.
  Defined.

  Hint Resolve InA_nil : test.
  Hint Resolve <- InA_nil : test.
  Hint Constructors ForallOrdPairs : test.

  Definition OkOk : forall instructions : list Instruction.t, Ok instructions -> Ok instructions.
  Proof.
    intros x Ok_x.
    split.
      induction Ok_x as [| x₀ Ok_x₀ IHx₀ owner not_InUp_owner In_Down_owner| x₀ Ok_x₀ IHx₀ owner not_In_Down_owner].
          constructor.
        constructor 2 with (2 := IHx₀).
        eapply Forall_impl, not_InA_iff with (1 := not_InUp_owner).
        intros [opcode' owner'] neq owner_eq_owner'.
        now eapply Instruction.ap_left', Opcode.not_Up in neq.
      constructor 2 with (2 := IHx₀).
      assert (not_In_owner : Forall (fun instruction => ~ Owner.eq owner (Instruction.operand instruction)) x₀).
        assert (not_In_Up_owner : ~ InA Instruction.eq (Opcode.Up, owner) x₀).
          contradict not_In_Down_owner; now apply Up_impl_Down.
        eapply Forall_impl.
        2: {
          apply Forall_and; apply not_InA_iff.
            exact not_In_Up_owner.
          exact not_In_Down_owner.
        }
        intros [[|] owner']; firstorder.
      now apply Forall_impl with (2 := not_In_owner).
    intros owner.
    now apply Up_impl_Down.
  Qed. *)

  Module Block.
    Import Coq.FSets.FMaps.

  Module Owner' :=  Backport_DT Owner.
  Module Regular (Map : WSfun Owner').
    Module Import Facts := WFacts_fun Owner' Map.

    Module Coloring := Coloring Owner' Map.
    Definition Ok := Ok.Ok.

    Lemma not_InA_iff : forall (A : Type) (eqA : A -> A -> Prop) (u : A) (y : list A),
      ~ InA eqA u y <->
      Forall (fun v => ~ eqA u v) y.
    Proof.
      intros A eqA u y.
      now rewrite InA_altdef, <- Forall_Exists_neg.
    Qed.

    Definition Forall_iff : forall (A : Type) (P : A -> Prop) (u₀ : A) (x₀ : list A), Forall P (u₀ :: x₀) <-> P u₀ /\ Forall P x₀.
    Proof.
      intros A P u₀ x₀.
      split.
        intros Forall_x.
        constructor.
          now apply Forall_inv with x₀.
        now apply Forall_inv_tail with u₀.
      intros [P_u₀ Forall_x₀].
      now constructor.
    Defined.

      Definition Coloring_Ok (instructions : list Instruction.t) (coloring : Coloring.t) : Prop :=
        Coloring.Ok coloring /\ (forall owner : Owner.t,
        (Ok.Active owner instructions ->
        Coloring.Contains coloring owner) /\
        (Ok.InUp owner instructions ->
        ~ Coloring.Contains coloring owner)).

    Module Color.
      Definition Ok
        (instructions : list Instruction.t)
        (coloring : Coloring.t)
        (color : nat) :
        Prop :=
        exists owner : Owner.t,
          Coloring.MapsTo coloring owner color /\
          ~ Ok.InDown owner instructions.
      
      Lemma add_Up_eq
        (coloring : Coloring.t)
        (instructions : list Instruction.t)
        (color : nat)
        (owner : Owner.t) :
        Ok instructions coloring color ->
        ~ Coloring.Contains coloring owner ->
        Ok (Ok.add_Up owner instructions) (Coloring.add_eq coloring owner) color.
      Proof.
        intros (owner' & owner'_to_color & not_InDown_owner') not_In_owner.
        unfold Ok.
        exists owner'; split.
          apply Map.add_2.
            contradict not_In_owner.
            unfold Coloring.Contains.
            rewrite not_In_owner; now exists color.
          assumption.
        now apply Ok.not_InDown_add_Up.
      Qed.

      Lemma Color_Ok_add_Up_lt
        (coloring : Coloring.t)
        (instructions : list Instruction.t)
        (color color' : nat)
        (owner : Owner.t) :
        Ok instructions coloring color ->
        ~ Coloring.Contains coloring owner ->
        Ok (Ok.add_Up owner instructions) (Coloring.add_lt coloring owner color') color.
      Proof.
        intros (owner' & owner'_to_color & not_InDown_owner') not_In_owner.
        unfold Ok.
        exists owner'; split.
          apply Map.add_2.
            contradict not_In_owner.
            unfold Coloring.Contains.
            rewrite not_In_owner; now exists color.
          assumption.
        now apply Ok.not_InDown_add_Up.
      Qed.
    End Color.

    Fixpoint regular
      (instructions : list Instruction.t)
      (coloring : Coloring.t)
      (unused_colors : list nat) :
      option Coloring.t :=
      match instructions, unused_colors with
      | (Opcode.Up, owner) :: tail, [] => regular
        tail
        (Coloring.add_eq coloring owner)
        []
      | (Opcode.Up, owner) :: tail, color :: unused_colors => regular
        tail
        (Coloring.add_lt coloring owner color)
        unused_colors
      | (Opcode.Down, owner) :: tail, unused_colors =>
          bind (Coloring.find' coloring owner) (fun color => 
          regular
            tail
            coloring
            (color :: unused_colors))
      | [], _ => ret coloring
      end.

    Module Type InvariantType.
      Parameter P : list Instruction.t -> Coloring.t -> list nat -> option Coloring.t -> Prop.

      Section Properties.
        Variable owner : Owner.t.
        Variable instructions : list Instruction.t.
        Variable coloring : Coloring.t.
        Variable color : nat.
        Variable unused_colors : list nat.
        Variable result : option Coloring.t.

        Parameter P_nil :
          P [] coloring unused_colors (Some coloring).

        Parameter P_Up_eq :
          P instructions (Coloring.add_eq coloring owner) [] result ->
          P ((Opcode.Up, owner) :: instructions) coloring [] result.

        Parameter P_Up_lt :
          P instructions (Coloring.add_lt coloring owner color) unused_colors result ->
          P ((Opcode.Up, owner) :: instructions) coloring (color :: unused_colors) result.

        Parameter P_Down_Some :
          Coloring.MapsTo coloring owner color ->
          P instructions coloring (color :: unused_colors) result ->
          P ((Opcode.Down, owner) :: instructions) coloring unused_colors result.

        Parameter P_Down_None :
          ~ Coloring.Contains coloring owner ->
          P ((Opcode.Down, owner) :: instructions) coloring unused_colors None.
      End Properties.
    End InvariantType.

    Module InvariantFacts (Import I : InvariantType).
      Lemma correct : forall
        (instructions : list Instruction.t)
        (coloring : Coloring.t)
        (unused_colors : list nat),
        P instructions coloring unused_colors (regular instructions coloring unused_colors).
      Proof.
        induction instructions as [| [[|] owner] instructions IHinstructions];
        intros
          coloring
          unused_colors.
            apply P_nil.
          destruct unused_colors as [| color unused_colors]; simpl.
            specialize (IHinstructions (Coloring.add_eq coloring owner) []).
            now apply P_Up_eq.
          specialize (IHinstructions (Coloring.add_lt coloring owner color) unused_colors).
          now apply P_Up_lt.
        simpl.
        destruct (Coloring.find' coloring owner) as [color|] eqn: find; simpl.
          specialize (IHinstructions coloring (color :: unused_colors)).
          apply find_mapsto_iff in find.
          now apply P_Down_Some with color.
        apply not_find_in_iff in find.
        now apply P_Down_None.
      Qed.
    End InvariantFacts.

    Definition UnusedColors_Ok
      (coloring : Coloring.t)
      (instructions : list Instruction.t)
      (unused_colors : list nat) :
      Prop :=
      Forall (Color.Ok instructions coloring) unused_colors.

    Inductive Subsets (A : Type) (P : list A -> Prop) : list A -> Prop :=
    | Subsets_nil : Subsets P []
    | Subsets_cons : forall (u₀ : A) (x₀ : list A),
      P (u₀ :: x₀) -> Subsets P x₀ -> Subsets P (u₀ :: x₀).

    Definition RealColoring
      (coloring : Coloring.t)
      (instructions : list Instruction.t) :
      Prop :=
      forall owner owner' : Owner.t,
        ~ Owner.eq owner owner' ->
        Ok.Active owner instructions ->
        Ok.Active owner' instructions ->
        exists color color' : nat,
          Coloring.MapsTo coloring owner color /\
          Coloring.MapsTo coloring owner' color' /\
          color <> color'.

    Inductive OptionSpec (A : Type) (P : A -> Prop) (Q : Prop) : option A -> Prop :=
    | OptionSpec_Some : forall u : A, P u -> OptionSpec P Q (Some u)
    | OptionSpec_None : Q -> OptionSpec P Q None.
    #[global]
    Hint Constructors OptionSpec : core.

    Module Invariant <: InvariantType.
      Definition P
        (instructions : list Instruction.t)
        (coloring : Coloring.t)
        (unused_colors : list nat)
        (result : option Coloring.t) :
        Prop :=
        Ok.Ok instructions ->
        Coloring_Ok instructions coloring ->
        UnusedColors_Ok coloring instructions unused_colors ->
        OptionSpec Coloring.Ok False result.

      Section Properties.
        Variable owner : Owner.t.
        Variable instructions : list Instruction.t.
        Variable coloring : Coloring.t.
        Variable color : nat.
        Variable unused_colors : list nat.
        Variable result : option Coloring.t.

        Ltac P_intros :=
          intros
            Ok_instructions
            [Ok_coloring Ok'_coloring]
            Ok_unused_colors.

        Lemma P_nil :
          P [] coloring unused_colors (Some coloring).
        Proof.
          P_intros.
          now constructor.
        Qed.

        Lemma P_Up_eq :
          P instructions (Coloring.add_eq coloring owner) [] result ->
          P ((Opcode.Up, owner) :: instructions) coloring [] result.
        Proof.
          intros IHP; P_intros.
          apply Ok.cons_Up_iff in Ok_instructions as (Active_owner & Ok_instructions).
          assert (not_In_owner : ~ Coloring.Contains coloring owner).
            now apply Ok'_coloring; left.
          apply IHP.
              assumption.
            split.
              now apply Coloring.Ok.add_eq, Ok'_coloring; [| left].
            intros owner'.
            unfold Coloring.Contains; simpl.
            rewrite add_in_iff.
            split.
              intros Active_owner'.
              destruct (Owner.eq_dec owner owner') as
                [owner_eq_owner'| owner_neq_owner'];
                [now left| right].
              apply Ok'_coloring, Ok.Active_cons_Up.
              split.
                now contradict owner_neq_owner'.
              assumption.
            intros InUp_owner'.
            enough (~ Owner.eq owner owner' /\ ~ Map.In owner' (Coloring.labeling coloring)) by firstorder.
            split.
              now apply Ok.InUp_Active with instructions.
            now apply Ok'_coloring; right.
          constructor.
        Qed.

        Lemma P_Up_lt :
          P instructions (Coloring.add_lt coloring owner color) unused_colors result ->
          P ((Opcode.Up, owner) :: instructions) coloring (color :: unused_colors) result.
        Proof.
          intros IHP; P_intros.
          apply Ok.cons_Up_iff in Ok_instructions as (Active_owner & Ok_instructions).
          apply Forall_iff in Ok_unused_colors as (Ok_color & Ok_unused_colors).
          assert (not_In_owner : ~ Coloring.Contains coloring owner).
            now apply Ok'_coloring; left.
          apply IHP.
              assumption.
            split.
              apply Coloring.Ok.add_lt; try auto.
              apply Ok_coloring.
              destruct Ok_color as (owner' &  ? & ?).
              now exists owner'.
            intros owner'.
            unfold Coloring.Contains; simpl.
            rewrite add_in_iff.
            split.
            intros Active_owner'.
            destruct (Owner.eq_dec owner owner') as
              [owner_eq_owner'| owner_neq_owner'];
              [now left| right].
            apply Ok'_coloring, Ok.Active_cons_Up.
              split.
                now contradict owner_neq_owner'.
              assumption.
            intros InUp_owner'.
            enough (~ Owner.eq owner owner' /\ ~ Map.In owner' (Coloring.labeling coloring)) by firstorder.
            split.
              now apply Ok.InUp_Active with instructions.
            now apply Ok'_coloring; right.
          eapply Forall_impl with (2 := Ok_unused_colors).
          intros n (owner' & owner'_to_n & not_InDown_owner').
          apply Ok.not_InDown_add_Up in not_InDown_owner'.
          exists owner'; split; try assumption.
          apply Map.add_2.
            now apply Ok.not_InDown_Active with instructions.
          assumption.
        Qed.

        Lemma P_Down_Some :
          Coloring.MapsTo coloring owner color ->
          P instructions coloring (color :: unused_colors) result ->
          P ((Opcode.Down, owner) :: instructions) coloring unused_colors result.
        Proof.
          intros owner_to_color IHP; P_intros.
          apply Ok.cons_Down_iff in Ok_instructions as (not_InUp_owner & Ok_tail).
          unfold Coloring.find'.
          apply IHP.
              assumption.
            split.
              assumption.
            intros owner'.
            split.
              intros Active_owner'.
              now apply Ok'_coloring, Ok.Active_cons_Down; [constructor| right].
            intros InUp_owner'.
            now apply Ok'_coloring, Ok.InUp_add_Down.
          constructor.
          exists owner.
            now split.
          eapply Forall_impl with (2 := Ok_unused_colors).
          intros n (owner' & owner'_to_color & not_InDown_owner').
          exists owner'; split.
            assumption.
          now apply Ok.not_InDown_add_Down in not_InDown_owner'.
        Qed.

        Lemma P_Down_None :
          ~ Coloring.Contains coloring owner ->
          P ((Opcode.Down, owner) :: instructions) coloring unused_colors None.
        Proof.
          intros not_In_owner; P_intros.
          apply Ok.cons_Down_iff in Ok_instructions as (not_InUp_owner & Ok_tail).
          contradict not_In_owner.
          now apply Ok'_coloring, Ok.Active_cons_Down; constructor.
        Qed.
      End Properties.
    End Invariant.

    Module Import InvariantFacts' := InvariantFacts Invariant.
    Lemma regular_Ok : forall
      (instructions : list Instruction.t )
      (coloring : Coloring.t)
      (unused_colors : list nat),
      Ok.Ok instructions ->
      Coloring_Ok instructions coloring ->
      UnusedColors_Ok coloring instructions unused_colors ->
      OptionSpec
        (Coloring.Ok.t)
        False
        (regular instructions coloring unused_colors).
    Proof.
      apply correct.
    Qed.
  End Regular.
End Block.
End Assigned.

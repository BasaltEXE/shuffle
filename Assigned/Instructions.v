Require Import Coq.Structures.Equalities.
Require Import Coq.Lists.SetoidList.
Import ListNotations.

Require Import Shuffle.List.
Require Shuffle.Instruction.

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

Module Make (Operand : DecidableTypeBoth).
  Module Instruction := Instruction.Make Opcode Operand.

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

  Inductive Ok : t -> Prop :=
  | nil : Ok []
  | cons_Up : forall (p₀ : Operand.t) (x₀ : t),
    Active p₀ x₀ ->
    Ok x₀ ->
    Ok (Up p₀ :: x₀)
  | cons_Down : forall (p₀ : Operand.t) (x₀ : t),
    Absent p₀ x₀ ->
    Ok x₀ ->
    Ok (Down p₀ :: x₀).

  Definition Closed
    (x : t) :
    Prop :=
      forall p : Operand.t,
      In (Down p) x -> Ahead p x.

  Lemma Closed_not_Active :
    forall
      (p : Operand.t)
      (x : t),
      Closed x ->
      ~ Active p x.
  Proof.
    intros p x Closed_x (not_Ahead_p & H).
    now contradict not_Ahead_p; apply Closed_x.
  Qed.

  Module Orthogonal.
    Section Orthogonal.
      Variables
        (v w : Operand.t)
        (x : t).

      Lemma Up_impl_Down :
        Ok x ->
        Ahead v x ->
        In (Down v) x.
      Proof.
        intros Ok_x.
        induction Ok_x as [| p₀ x₀ Active_p₀ Ok_x₀ IHx₀| p₀ x₀ Absent_p₀ Ok_x₀ IHx₀];
          intros Ahead_v; [easy| ..].
          1 - 2:
          apply InA_cons in Ahead_v as [(eq & v_eq_p₀)| Ahead_v];
          [change (Operand.eq v p₀) in v_eq_p₀| now right; apply IHx₀].
            now rewrite v_eq_p₀; right.
          now contradict eq; apply Opcode.not_Up_iff_Down.
      Qed.

      Lemma Ahead_Active :
        Ahead v x ->
        Active w x ->
        ~ Operand.eq v w.
      Proof.
        intros Ahead_v Active_w v_eq_w.
        now rewrite v_eq_w in Ahead_v.
      Qed.

      Lemma Active_Absent :
        Active v x ->
        Absent w x ->
        ~ Operand.eq v w.
      Proof.
        intros Active_v Absent_w v_eq_w.
        now rewrite v_eq_w in Active_v.
      Qed.

      Lemma Ahead_Absent :
        Ok x ->
        Ahead v x ->
        Absent w x ->
        ~ Operand.eq v w.
      Proof.
        intros Ok_x Ahead_v Absent_v.
        contradict Absent_v; rewrite <- Absent_v.
        now apply Up_impl_Down.
      Qed.
    End Orthogonal.

    Module Hints.
      Ltac solve_neq :=
        match goal with
        | |- ~ Operand.eq ?v ?w => change(complement Operand.eq v w)
        end;
        (idtac + symmetry);
        match goal with
        | |- complement Operand.eq ?v ?w =>
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
      Hint Extern 2 (~ (Operand.eq _ _)) => solve_neq : instructions.
    End Hints.
  End Orthogonal.

  Module Ok.
    Section Ok.
      Variables
        (p₀ v : Operand.t)
        (u₀ : Instruction.t)
        (x₀ x : t).

      Lemma cons_inv :
        Ok (u₀ :: x₀) ->
        Ok x₀.
      Proof.
        now inversion 1.
      Qed.

      Lemma cons_Up_inv :
        Ok (Up p₀ :: x₀) ->
        Active p₀ x₀.
      Proof.
        intros Ok_x₀.
        now inversion_clear Ok_x₀.
      Qed.

      Lemma cons_Down_inv :
        Ok (Down p₀ :: x₀) ->
        Absent p₀ x₀.
      Proof.
        intros Ok_x₀.
        now inversion_clear Ok_x₀.
      Qed.

      Lemma nil_iff :
        Ok [] <->
        True.
      Proof.
        now split; [| constructor].
      Qed.

      Lemma cons_Up_iff :
        Ok (Up p₀ :: x₀) <->
          Active p₀ x₀ /\
          Ok x₀.
      Proof.
        now split; [inversion_clear 1| constructor].
      Qed.

      Lemma cons_Down_iff :
        Ok (Down p₀ :: x₀) <->
          Absent p₀ x₀ /\
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

    Add Parametric Morphism : Ok with signature
      (Tail (A := Instruction.t)) ++> impl as Ok_morphism.
    Proof.
      intros x y (u₀ & x₀) Ok_x.
      now apply Ok.cons_inv with u₀.
    Qed.
  End Ok.

  Module Ahead.
    Section Ahead.
      Variables
        (p₀ v : Operand.t)
        (u₀ : Instruction.t)
        (x₀ : t).

      Lemma cons :
        Ahead v x₀ ->
        Ahead v (u₀ :: x₀).
      Proof.
        now right.
      Qed.

      Lemma cons_Up :
        Operand.eq p₀ v ->
        Ahead v (Up p₀ :: x₀).
      Proof.
        now intros p₀_eq_v; left.
      Qed.

      Lemma nil_inv :
        ~ Ahead v [].
      Proof.
        intros Ahead_v.
        apply InA_nil with (1 := Ahead_v).
      Qed.

      Lemma cons_Up_inv :
        Ahead v (Up p₀ :: x₀) ->
        ~ Operand.eq p₀ v ->
        Ahead v x₀.
      Proof.
        intros Ahead_v p₀_neq_v.
        now apply InA_cons in Ahead_v as [(_ & p₀_eq_v)| Ahead_v];
          [absurd (Operand.eq p₀ v)|].
      Qed.

      Lemma cons_Down_inv :
        Ahead v (Down p₀ :: x₀) ->
        Ahead v x₀.
      Proof.
        intros Ahead_v.
        now apply InA_cons in Ahead_v as [(Up_eq_Down & _)| Ahead_v];
          [contradict Up_eq_Down; apply Opcode.not_Up_iff_Down|].
      Qed.

      Lemma nil_iff :
        Ahead v [] <->
        False.
      Proof.
        now split; [apply nil_inv|].
      Qed.

      Lemma cons_Up_iff :
        Ahead v (Up p₀ :: x₀) <->
          Operand.eq p₀ v \/
          Ahead v x₀.
      Proof.
        split.
          now destruct (Operand.eq_dec p₀ v) as [p₀_eq_v| p₀_neq_v];
            [left| right; apply cons_Up_inv].
        now intros [p₀_eq_v| Ahead_v]; [left| right].
      Qed.

      Lemma cons_Up_neq_iff :
        ~ Operand.eq p₀ v ->
          Ahead v (Up p₀ :: x₀) <->
            Operand.eq p₀ v \/
            Ahead v x₀.
      Proof.
        now rewrite cons_Up_iff.
      Qed.

      Lemma cons_Down_iff :
        Ahead v (Down p₀ :: x₀) <->
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
        (p₀ v : Operand.t)
        (x₀ : t).

      Lemma cons_Up :
        ~ Operand.eq p₀ v ->
        Active v x₀ ->
        Active v (Up p₀ :: x₀).
      Proof.
        intros p₀_neq_v Active_v.
        split; [| now right].
        now apply not_InA_cons; split;
          [apply Instruction.neq_operand; contradict p₀_neq_v|].
      Qed.

      Lemma cons_Down :
        Active v x₀ ->
        Active v (Down p₀ :: x₀).
      Proof.
        intros Active_v.
        split; [| now right].
        now apply not_InA_cons; split;
          [apply Instruction.neq_opcode, Opcode.not_Up_iff_Down|].
      Qed.

      Lemma cons_Down_eq :
        Ok (Down p₀ :: x₀) ->
        Operand.eq p₀ v ->
        Active v (Down p₀ :: x₀).
      Proof.
        intros Ok_instructions p₀_eq_v.
        apply Ok.cons_Down_iff in Ok_instructions as (Absent_p₀ & Ok_instructions).
        split; [| now left].
        contradict p₀_eq_v; apply Ahead.cons_Down_inv in p₀_eq_v.
        Orthogonal.Hints.solve_neq.
      Qed.

      Lemma nil_inv : ~ Active v [].
      Proof.
        intros (_ & In_Down_v).
        apply InA_nil with (1 := In_Down_v).
      Qed.

      Lemma cons_Up_inv :
        Active v (Up p₀ :: x₀) ->
        Active v x₀.
      Proof.
        intros (not_Ahead_v & In_Down_v).
        split.
          now contradict not_Ahead_v; right.
        now apply InA_cons in In_Down_v as [(Down_eq_Up & _)| In_Down_v];
          [contradict Down_eq_Up; apply Opcode.not_Down_iff_Up|].
      Qed.

      Lemma cons_Down_inv :
        Active v (Down p₀ :: x₀) ->
        ~ Operand.eq p₀ v ->
        Active v x₀.
      Proof.
        intros (not_Ahead_v & In_Down_v) p₀_neq_v.
        split.
          now contradict not_Ahead_v; right.
        now apply InA_cons in In_Down_v as [(_ & v_eq_p₀)| In_Down_v];
          [absurd (Operand.eq p₀ v)|].
      Qed.

      Lemma nil_iff :
        Active v [] <->
        False.
      Proof.
        now split; [apply nil_inv|].
      Qed.

      Lemma cons_Up_iff :
        Active v (Up p₀ :: x₀) <->
          ~ Operand.eq p₀ v /\
          Active v x₀.
      Proof.
        split.
          intros Active_v; split.
            assert (Ahead_p₀ : Ahead p₀ (Up p₀ :: x₀)) by now left.
            Orthogonal.Hints.solve_neq.
          now apply cons_Up_inv.
        now intros (p₀_eq_v & Active_v); apply cons_Up.
      Qed.

      Lemma cons_Up_neq_iff :
        ~ Operand.eq p₀ v ->
          Active v (Up p₀ :: x₀) <->
          Active v x₀.
      Proof.
        now rewrite cons_Up_iff.
      Qed.

      Lemma cons_Down_iff :
        Ok (Down p₀ :: x₀) ->
          Active v (Down p₀ :: x₀) <->
            Operand.eq p₀ v \/
            Active v x₀.
      Proof.
        intros Ok_instructions.
        split.
          destruct (Operand.eq_dec p₀ v) as [p₀_eq_v| p₀_neq_v];
            [now left| right].
          now apply cons_Down_inv.
        now intros [p₀_eq_v| Active_v];
          [apply cons_Down_eq| apply cons_Down].
      Qed.

      Lemma cons_Down_neq_iff :
        Ok (Down p₀ :: x₀) ->
        ~ Operand.eq p₀ v ->
          Active v (Down p₀ :: x₀) <->
          Active v x₀.
      Proof.
        intros Ok_x; rewrite cons_Down_iff; tauto.
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
        (p₀ v : Operand.t)
        (u₀ : Instruction.t)
        (x₀ : t).

      Lemma nil :
        Absent v [].
      Proof.
        unfold not; apply InA_nil.
      Qed.

      Lemma cons_Up :
        Absent v x₀ ->
        Absent v (Up p₀ :: x₀).
      Proof.
        intros Absent_v.
        now apply not_InA_cons; split;
          [apply Instruction.neq_opcode, Opcode.not_Down_iff_Up|].
      Qed.

      Lemma cons_Down :
        ~ Operand.eq p₀ v ->
        Absent v x₀ ->
        Absent v (Down p₀ :: x₀).
      Proof.
        intros p₀_neq_v Absent_v.
        now apply not_InA_cons; split;
          [apply Instruction.neq_operand; contradict p₀_neq_v|].
      Qed.

      Lemma cons_inv :
        Absent v (u₀ :: x₀) ->
        Absent v x₀.
      Proof.
        intros Absent_v.
        now apply not_InA_cons in Absent_v.
      Qed.

      Lemma nil_iff :
        Absent v [] <->
        True.
      Proof.
        easy.
      Qed.

      Lemma cons_Down_iff :
        Absent v (Down p₀ :: x₀) <->
          ~ Operand.eq p₀ v /\
          Absent v x₀.
      Proof.
        split; intros Absent_v; [| now apply cons_Down].
        apply not_InA_cons in Absent_v as (v_neq_p₀ & Absent_v).
        apply Instruction.neq_eq_opcode in v_neq_p₀; [| reflexivity].
        now split; [contradict v_neq_p₀|].
      Qed.

      Lemma cons_Down_neq_iff :
        ~ Operand.eq p₀ v ->
          Absent v (Down p₀ :: x₀) <->
          Absent v x₀.
      Proof.
        now rewrite cons_Down_iff.
      Qed.

      Lemma cons_Up_iff :
        Absent v (Up p₀ :: x₀) <->
        Absent v x₀.
      Proof.
        split.
          intros Absent_v.
          now apply not_InA_cons with (Up p₀).
        now intros Absent_v; apply not_InA_cons; split;
          [apply Instruction.neq_opcode, Opcode.not_Down_iff_Up|].
      Qed.
    End Absent.

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
End Make.

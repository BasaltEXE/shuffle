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
  | nil :
    Ok []
  | cons_Up :
    forall
      (p₀ : Operand.t)
      (x₀ : t),
      Active p₀ x₀ ->
      Ok x₀ ->
      Ok (Up p₀ :: x₀)
  | cons_Down :
    forall
      (p₀ : Operand.t)
      (x₀ : t),
      Absent p₀ x₀ ->
      Ok x₀ ->
      Ok (Down p₀ :: x₀).

  Definition Closed
    (x : t) :
    Prop :=
      forall
        p : Operand.t,
        In (Down p) x -> Ahead p x.

  Lemma Closed_impl_not_Active :
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
        (v : Operand.t)
        (x : t).

      Lemma Up_impl_Down :
        Ok x ->
        Ahead v x ->
        In (Down v) x.
      Proof.
        intros Ok_x.
        induction Ok_x as [| p₀ x₀ Active_p₀_x₀ Ok_x₀ IHx₀| p₀ x₀ Absent_p₀_x₀ Ok_x₀ IHx₀];
          intros Ahead_v_x; [easy| ..].
          1 - 2:
          apply InA_cons in Ahead_v_x as [(eq & v_eq_p₀)| Ahead_v_x₀];
          [change (Operand.eq v p₀) in v_eq_p₀| now right; apply IHx₀].
            now rewrite v_eq_p₀; right.
          now contradict eq; apply Opcode.not_Up_iff_Down.
      Qed.

      Lemma Ahead_Active :
        Ahead v x ->
        Active v x ->
        False.
      Proof.
        now intros Ahead_v_x Active_v_x.
      Qed.

      Lemma Active_Absent :
        Active v x ->
        Absent v x ->
        False.
      Proof.
        now intros Active_v_x Absent_v_x.
      Qed.

      Lemma Ahead_Absent :
        Ok x ->
        Ahead v x ->
        Absent v x ->
        False.
      Proof.
        intros Ok_x Ahead_v_x Absent_v_x.
        contradict Absent_v_x.
        now apply Up_impl_Down.
      Qed.

      Lemma Active_impl_not_Ahead :
        Active v x ->
        ~ Ahead v x.
      Proof.
        now intros Active_v_x Ahead_v_x; apply Ahead_Active.
      Qed.

      Lemma Absent_impl_not_Ahead :
        Ok x ->
        Absent v x ->
        ~ Ahead v x.
      Proof.
        now intros Ok_x Absent_v_x Ahead_v_x; apply Ahead_Absent.
      Qed.

      Lemma Ahead_impl_not_Active :
        Ahead v x ->
        ~ Active v x.
      Proof.
        now intros Ahead_v_x Active_v_x; apply Ahead_Active.
      Qed.

      Lemma Absent_impl_not_Active :
        Absent v x ->
        ~ Active v x.
      Proof.
        now intros Absent_v_x Active_v_x; apply Active_Absent.
      Qed.

      Lemma Ahead_impl_not_Absent :
        Ok x ->
        Ahead v x ->
        ~ Absent v x.
      Proof.
        now intros Ok_x Ahead_v_x Absent_v_x; apply Ahead_Absent.
      Qed.

      Lemma Active_impl_not_Absent :
        Active v x ->
        ~ Absent v x.
      Proof.
        now intros Active_v_x Absent_v_x; apply Active_Absent.
      Qed.
    End Orthogonal.

    Module Hints.
      #[export]
      Hint Resolve Active_impl_not_Ahead : instructions.
      #[export]
      Hint Resolve Absent_impl_not_Ahead : instructions.
      #[export]
      Hint Resolve Ahead_impl_not_Active : instructions.
      #[export]
      Hint Resolve Absent_impl_not_Active : instructions.
      #[export]
      Hint Resolve Ahead_impl_not_Absent : instructions.
      #[export]
      Hint Resolve Active_impl_not_Absent : instructions.
    End Hints.
  End Orthogonal.
  Import Orthogonal.Hints.

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
      Hint Immediate cons_inv : instructions.
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
  Import Ok.Hints.

  Ltac instructions_tac :=
    eauto with instructions.

  Module Ahead.
    Section Ahead.
      Variables
        (p₀ v : Operand.t)
        (u₀ : Instruction.t)
        (x₀ : t).

      Lemma nil :
        ~ Ahead v [].
      Proof.
        intros Ahead_v_x.
        apply InA_nil with (1 := Ahead_v_x).
      Qed.

      Lemma cons_Up_hd :
        Ahead p₀ (Up p₀ :: x₀).
      Proof.
        now left.
      Qed.

      Lemma cons_Down_hd :
        Ok (Down p₀ :: x₀) ->
        ~ Ahead p₀ (Down p₀ :: x₀).
      Proof with instructions_tac.
        intros Ok_x.
        enough (not_Ahead_p₀_x₀ : ~ Ahead p₀ x₀)...
        now apply not_InA_cons;
          enough (Opcode.Up <> Opcode.Down) by firstorder.
      Qed.

      Lemma cons_tl :
        Ahead v x₀ ->
        Ahead v (u₀ :: x₀).
      Proof.
        now right.
      Qed.

      Lemma nil_iff :
        Ahead v [] <->
        False.
      Proof.
        now split; [apply nil|].
      Qed.

      Lemma cons_Up_iff :
        Ahead v (Up p₀ :: x₀) <->
          Operand.eq p₀ v \/
          Ahead v x₀.
      Proof.
        split.
          intros Ahead_v_x.
          destruct (Operand.eq_dec p₀ v) as [p₀_eq_v| p₀_neq_v];
            [now left| right].
          now apply InA_cons in Ahead_v_x as [(_ & p₀_eq_v)| Ahead_v_x₀];
            [absurd (Operand.eq p₀ v)|].
        now intros [p₀_eq_v| Ahead_v_x₀]; [left| right].
      Qed.

      Lemma cons_Down_iff :
        Ahead v (Down p₀ :: x₀) <->
        Ahead v x₀.
      Proof.
        split.
          intros Ahead_v_x.
          now apply InA_cons in Ahead_v_x as [(Up_eq_Down & _)| Ahead_v_x₀];
            [contradict Up_eq_Down; apply Opcode.not_Up_iff_Down|].
        now intros Ahead_v_x₀; right.
      Qed.
    End Ahead.

    Module Hints.
      #[export]
      Hint Resolve nil : instructions.
      #[export]
      Hint Resolve cons_Up_hd : instructions.
      #[export]
      Hint Resolve cons_Down_hd : instructions.
      #[export]
      Hint Resolve cons_tl : instructions.
    End Hints.
  End Ahead.
  Import Ahead.Hints.

  Module Active.
    Section Active.
      Variables
        (p₀ v : Operand.t)
        (x₀ : t).

      Lemma nil : ~ Active v [].
      Proof.
        intros (_ & In_Down_v).
        apply InA_nil with (1 := In_Down_v).
      Qed.

      Lemma cons_Up_hd :
        ~ Active p₀ (Up p₀ :: x₀).
      Proof with instructions_tac.
        enough (Ahead p₀ (Up p₀ :: x₀))...
      Qed.

      Lemma cons_Up_tl :
        ~ Operand.eq p₀ v ->
        Active v x₀ ->
        Active v (Up p₀ :: x₀).
      Proof.
        intros p₀_neq_v Active_v_x₀.
        constructor; [| now right].
        rewrite Ahead.cons_Up_iff; tauto.
      Qed.

      Lemma cons_Down_hd :
        Ok (Down p₀ :: x₀) ->
        Active p₀ (Down p₀ :: x₀).
      Proof with instructions_tac.
        intros Ok_instructions.
        constructor; [| now left].
        rewrite Ahead.cons_Down_iff...
      Qed.

      Lemma cons_Down_tl :
        Active v x₀ ->
        Active v (Down p₀ :: x₀).
      Proof with instructions_tac.
        intros Active_v.
        constructor; [| now right].
        rewrite Ahead.cons_Down_iff...
      Qed.

      Lemma nil_iff :
        Active v [] <->
        False.
      Proof.
        now split; [apply nil|].
      Qed.

      Lemma cons_Up_iff :
        Active v (Up p₀ :: x₀) <->
          ~ Operand.eq p₀ v /\
          Active v x₀.
      Proof.
        split.
          intros (not_Ahead_v_x & In_Down_v_x).
          assert (~ Operand.eq p₀ v /\ ~ Ahead v x₀) as
            (p₀_neq_v & not_Ahead_v_x₀) by
            (rewrite Ahead.cons_Up_iff in not_Ahead_v_x; tauto).
          enough (In (Down v) x₀) by firstorder.
          now enough (Opcode.Down <> Opcode.Up);
            [apply InA_cons in In_Down_v_x; firstorder|].
        now intros (p₀_neq_v & Active_v_x₀); apply cons_Up_tl.
      Qed.

      Lemma cons_Down_iff :
        Ok (Down p₀ :: x₀) ->
          Active v (Down p₀ :: x₀) <->
            Operand.eq p₀ v \/
            Active v x₀.
      Proof.
        intros Ok_instructions.
        split.
          intros (not_Ahead_v_x & In_Down_v_x).
          destruct (Operand.eq_dec p₀ v) as [p₀_eq_v| p₀_neq_v];
            [now left| right].
          apply InA_cons in In_Down_v_x.
          enough (~ Operand.eq v p₀); firstorder.
        now intros [<-| Active_v];
          [apply cons_Down_hd| apply cons_Down_tl].
      Qed.
    End Active.

    Module Hints.
      #[export]
      Hint Resolve nil : instructions.
      #[export]
      Hint Resolve cons_Up_hd : instructions.
      #[export]
      Hint Resolve cons_Up_tl : instructions.
      #[export]
      Hint Resolve cons_Down_hd : instructions.
      #[export]
      Hint Resolve cons_Down_tl : instructions.
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

      Lemma cons_Up_hd :
        Ok (Up p₀ :: x₀) ->
        ~ Absent p₀ (Up p₀ :: x₀).
      Proof.
        instructions_tac.
      Qed.

      Lemma cons_Up_tl :
        Absent v x₀ ->
        Absent v (Up p₀ :: x₀).
      Proof.
        intros Absent_v.
        now apply not_InA_cons; split;
          [apply Instruction.neq_opcode, Opcode.not_Down_iff_Up|].
      Qed.

      Lemma cons_Down_hd :
        ~ Absent p₀ (Down p₀ :: x₀).
      Proof.
        enough (In (Down p₀) (Down p₀ :: x₀)) by firstorder.
        now constructor.
      Qed.

      Lemma cons_Down_tl :
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
        split; intros Absent_v; [| now apply cons_Down_tl].
        apply not_InA_cons in Absent_v as (v_neq_p₀ & Absent_v).
        apply Instruction.neq_eq_opcode in v_neq_p₀; [| reflexivity].
        now split; [contradict v_neq_p₀|].
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
      Hint Resolve cons_Up_hd : instructions.
      #[export]
      Hint Resolve cons_Up_tl : instructions.
      #[export]
      Hint Resolve cons_Down_hd : instructions.
      #[export]
      Hint Resolve cons_Down_tl : instructions.

      #[export]
      Hint Immediate cons_inv : instructions.
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

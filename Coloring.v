Require Import Coq.FSets.FMaps.

Module Coloring (Owner : DecidableType) (Map : WSfun Owner).
Module Import Facts := WFacts_fun Owner Map.
  Definition t : Type :=
    nat * Map.t nat.

  Definition colors (self : t) : nat :=
    fst self.
  Definition labeling (self : t) : Map.t nat :=
    snd self.

  Definition empty : t :=
    (0, Map.empty nat).
  Definition add (self : t) (owner : Owner.t) (color : nat) : t :=
    (colors self, Map.add owner color (labeling self)).
  Definition increment (self : t) : t :=
    (S (colors self), labeling self).

  Definition add_lt (self : t) (owner : Owner.t) (color : nat) : t :=
    (colors self, Map.add owner color (labeling self)).
  Definition add_eq (self : t) (owner : Owner.t) : t :=
    (S (colors self), Map.add owner (colors self) (labeling self)).

  Definition find (self : t) (owner : Owner.t) : option nat :=
    Map.find owner (labeling self).

  Definition MapsTo (self : t) (owner : Owner.t) (color : nat) : Prop :=
    Map.MapsTo owner color (labeling self).
  Definition Contains (self : t) (owner : Owner.t) : Prop :=
    Map.In owner (labeling self).

  Module Ok.
    Definition t (self : Coloring.t) : Prop :=
      forall color : nat, color < colors self <-> (exists owner : Owner.t, MapsTo self owner color).

    Lemma empty : t Coloring.empty.
    Proof with auto with arith.
      intros color.
      split.
        intros color_lt_colors.
        contradict color_lt_colors; auto with arith.
      intros [owner owner_to_color].
      contradict owner_to_color.
      firstorder using empty_in_iff.
    Qed.

    Local Lemma not_In_neq : forall (owner owner' : Owner.t) (coloring : Map.t nat), ~ Map.In owner coloring -> Map.In owner' coloring -> ~ Owner.eq owner owner'.
    Proof.
      intros owner owner' coloring not_In_owner In_owner'.
      contradict not_In_owner.
      now rewrite not_In_owner.
    Defined.

    Lemma add_lt : forall coloring : Coloring.t, t coloring -> forall owner : Owner.t, ~ Coloring.Contains coloring owner -> forall color : nat, color < Coloring.colors coloring -> t (Coloring.add_lt coloring owner color).
    Proof.
      intros coloring Ok_coloring owner not_In_owner color color_lt_colors n.
      split.
        intros n_lt_colors.
        apply Ok_coloring in n_lt_colors as [owner' owner'_to_n].
        exists owner'; apply Map.add_2 with (2 := owner'_to_n).
        contradict not_In_owner.
        unfold Contains.
        rewrite not_In_owner; now exists n.
      intros [owner' owner'_to_n].
      apply add_mapsto_iff in owner'_to_n as [(_ & ->)| (_ & owner'_to_n)].
        assumption.
      now apply Ok_coloring; exists owner'.
    Qed.

    Lemma add_eq : forall coloring : Coloring.t, t coloring -> forall owner : Owner.t, ~ Coloring.Contains coloring owner -> t (Coloring.add_eq coloring owner).
    Proof.
      intros coloring Ok_coloring owner not_In.
      split.
        intros color_lt_S_colors.
        apply Lt.lt_n_Sm_le, PeanoNat.Nat.le_lteq in color_lt_S_colors as [color_lt_colors| ->].
          apply Ok_coloring in color_lt_colors as [owner' owner'_to_color].
          exists owner'.
          apply Map.add_2.
            apply not_In_neq with (Coloring.labeling coloring); firstorder.
          assumption.
        now exists owner; apply Map.add_1.
      intros [owner' owner'_to_color].
      apply add_mapsto_iff in owner'_to_color as [[eq <-]| [neq owner'_to_color]].
        auto.
      apply PeanoNat.Nat.lt_lt_succ_r, Ok_coloring.
      now exists owner'.
    Qed.
  End Ok.
End Coloring.

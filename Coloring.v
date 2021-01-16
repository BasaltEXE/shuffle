Require Import Coq.FSets.FMaps.

Module Coloring (Owner : DecidableType) (Map : WSfun Owner).
  Module Import Facts := WFacts_fun Owner Map.

  Definition Valid (colors : nat) (coloring : Map.t nat) : Prop :=
    forall color : nat, color < colors <-> (exists owner : Owner.t, Map.MapsTo owner color coloring).

  Lemma Valid_empty : Valid 0 (Map.empty _).
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

  Lemma Valid_add_lt : forall (colors : nat) (coloring : Map.t nat), Valid colors coloring -> forall owner : Owner.t, ~ Map.In owner coloring -> forall color : nat, color < colors -> Valid colors (Map.add owner color coloring).
  Proof.
    intros colors coloring Valid owner not_In color color_lt_colors n.
    split.
      intros n_lt_colors.
      apply Valid in n_lt_colors as [owner' owner'_to_n].
      exists owner'; apply Map.add_2 with (2 := owner'_to_n).
      contradict not_In.
      rewrite not_In; now exists n.
    intros [owner' owner'_to_n].
    apply add_mapsto_iff in owner'_to_n as [(_ & ->)| (_ & owner'_to_n)].
      assumption.
    now apply Valid; exists owner'.
  Qed.

  Lemma Valid_add_eq : forall (colors : nat) (coloring : Map.t nat), Valid colors coloring -> forall owner : Owner.t, ~ Map.In owner coloring -> Valid (S colors) (Map.add owner colors coloring).
  Proof.
    intros colors coloring Valid owner not_In.
    split.
      intros color_lt_S_colors.
      apply Lt.lt_n_Sm_le, PeanoNat.Nat.le_lteq in color_lt_S_colors as [color_lt_colors| ->].
        apply Valid in color_lt_colors as [owner' owner'_to_color].
        exists owner'.
        apply Map.add_2.
          apply not_In_neq with coloring; firstorder.
        assumption.
      now exists owner; apply Map.add_1.
    intros [owner' H].
    apply add_mapsto_iff in H as [[eq <-]| [neq H]].
      auto.
    apply PeanoNat.Nat.lt_lt_succ_r, Valid.
    now exists owner'.
  Qed.

  Create HintDb Valid.
  Hint Resolve Valid_empty Valid_add_eq Valid_add_lt : valid.

  Definition t : Type := {coloring : nat * Map.t nat | Valid (fst coloring) (snd coloring)}.

  Definition colors (self : t) : nat :=
    fst (proj1_sig self).

  Definition coloring (self : t) : Map.t nat :=
    snd (proj1_sig self).

  Definition valid (self : t) : Valid (colors self) (coloring self) :=
    proj2_sig self.

  Hint Resolve valid : valid.

  Definition Contains (self : t) (owner : Owner.t) : Prop :=
    Map.In owner (coloring self).

  Definition empty : t.
  Proof.
    exists (0, Map.empty nat).
    auto with valid.
  Qed.

  Lemma add_lt : forall (self : t) (owner : Owner.t), ~ Contains self owner -> forall color : nat, color < colors self -> t.
  Proof.
    intros self owner not_In_owner color color_lt_colors.
    exists (colors self, Map.add owner color (coloring self)).
    simpl; auto with valid.
  Qed.

  Lemma add_eq : forall (self : t) (owner : Owner.t), ~ Contains self owner -> t.
  Proof.
    intros self owner not_In_owner.
    exists (S (colors self), Map.add owner (colors self) (coloring self)).
    simpl; auto with valid.
  Qed.
End Coloring.
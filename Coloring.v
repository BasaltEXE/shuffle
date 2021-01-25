Require Import Coq.FSets.FMaps.
Require Import Coq.Program.Program.

Module Coloring (Owner : DecidableType) (Map : WSfun Owner).
  Module Import Facts := WFacts_fun Owner Map.

  Definition t : Type :=
    nat * Map.t nat.

  Definition colors (self : t) : nat :=
    fst self.
  Definition labeling (self : t) : Map.t nat :=
    snd self.

  Definition MapsTo (self : t) (owner : Owner.t) (color : nat) : Prop :=
    Map.MapsTo owner color (labeling self).
  Definition Contains (self : t) (owner : Owner.t) : Prop :=
    Map.In owner (labeling self).

  Program Definition find
    (self : t)
    (owner : Owner.t | Contains self owner) :
    {color : nat | MapsTo self owner color} :=
    match Map.find owner (labeling self) with
    | Some color => color
    | None => !
    end.
    Next Obligation.
      rename H into Contains_owner.
      now apply find_mapsto_iff.
    Qed.
    Next Obligation.
      now apply not_find_in_iff in H.
    Qed.

  Definition find'
    (self : t)
    (owner : Owner.t) :
    option nat :=
      Map.find owner (labeling self).

  Definition Ok (coloring : nat * Map.t nat) :=
    forall color : nat,
      color < colors coloring <->
      (exists owner : Owner.t, MapsTo coloring owner color).

  Definition empty :
    t :=
    (0, Map.empty nat).

  Definition add_lt
    (self : t)
    (owner : Owner.t)
    (color : nat) :
    t :=
    (colors self, Map.add owner color (labeling self)).

  Program Definition add_eq
    (self : t)
    (owner : Owner.t) :
    t :=
    (S (colors self), Map.add owner (colors self) (labeling self)).

  Module Ok.
    Definition t (coloring : Coloring.t) : Prop :=
      forall color : nat,
        color < colors coloring <->
        (exists owner : Owner.t, MapsTo coloring owner color).

    Lemma empty : t Coloring.empty.
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
    Qed.

    Lemma add_lt (self : Coloring.t) (owner : Owner.t) (color : nat) :
      t self ->
      ~ Coloring.Contains self owner ->
      color < colors self ->
      t (Coloring.add_lt self owner color).
    Proof.
      intros Ok_self not_In_owner color_lt_colors n.
      split.
        intros n_lt_colors.
        apply Ok_self in n_lt_colors as [owner' owner'_to_n].
        exists owner'; apply Map.add_2 with (2 := owner'_to_n).
        contradict not_In_owner.
        unfold Contains.
        rewrite not_In_owner; now exists n.
      intros [owner' owner'_to_n].
      apply add_mapsto_iff in owner'_to_n as [(_ & ->)| (_ & owner'_to_n)].
        assumption.
      now apply Ok_self; exists owner'.
    Qed.

    Lemma add_eq (self : Coloring.t) (owner : Owner.t) :
      t self ->
      ~ Coloring.Contains self owner ->
      t (Coloring.add_eq self owner).
    Proof.
      intros Ok_self not_In_owner.
      split.
        intros color_lt_S_colors.
        apply Lt.lt_n_Sm_le, PeanoNat.Nat.le_lteq in color_lt_S_colors as [color_lt_colors| ->].
          apply Ok_self in color_lt_colors as [owner' owner'_to_color].
          exists owner'.
          apply Map.add_2.
            apply not_In_neq with (Coloring.labeling self); firstorder.
          assumption.
        now exists owner; apply Map.add_1.
      intros [owner' owner'_to_color].
      apply add_mapsto_iff in owner'_to_color as [[eq <-]| [neq owner'_to_color]].
        auto.
      apply PeanoNat.Nat.lt_lt_succ_r, Ok_self.
      now exists owner'.
    Defined.
  End Ok.
End Coloring.

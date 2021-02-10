Require Import Coq.FSets.FMaps.
Require Import Coq.Program.Program.

Module Make (Owner : DecidableType) (Map : WSfun Owner).
  Module Import Facts := WFacts_fun Owner Map.

  Notation t :=
    (nat * Map.t nat)%type.

  Notation colors
    self :=
    (fst self)
    (only parsing).

  Notation labeling
    self :=
    (snd self)
    (only parsing).

  Notation empty :=
    (0, Map.empty nat)
    (only parsing).

  Notation add_lt
    self
    owner
    color :=
    (colors self, Map.add owner color (labeling self))
    (only parsing).

  Notation add_eq
    self
    owner :=
    (S (colors self), Map.add owner (colors self) (labeling self))
    (only parsing).

  Notation find
    self
    owner :=
    (Map.find owner (labeling self))
    (only parsing).

  Notation MapsTo
    self
    owner
    color :=
    (Map.MapsTo owner color (labeling self))
    (only parsing).

  Notation Contains
    self
    owner :=
    (Map.In owner (labeling self))
    (only parsing).

  Notation Ok
    self :=
    (forall color : nat,
      color < colors self <->
      (exists owner : Owner.t, MapsTo self owner color))
    (only parsing).

  Module Ok.
    Section Constructors.
      Variables
        (self : Make.t)
        (owner : Owner.t)
        (color : nat).

      Lemma empty :
        Ok Make.empty.
      Proof.
        clear self owner color; split.
          intros color_lt_colors.
          contradict color_lt_colors; auto with arith.
        intros [owner owner_to_color].
        contradict owner_to_color.
        firstorder using empty_in_iff.
      Qed.

      Lemma add_lt :
        Ok self ->
        ~ Contains self owner ->
        color < colors self ->
        Ok (Make.add_lt self owner color).
      Proof.
        intros Ok_self not_In_owner color_lt_colors n.
        split.
          intros n_lt_colors.
          apply Ok_self in n_lt_colors as [owner' owner'_to_n].
          exists owner'; apply Map.add_2 with (2 := owner'_to_n).
          contradict not_In_owner.
          rewrite not_In_owner; now exists n.
        intros [owner' owner'_to_n].
        apply add_mapsto_iff in owner'_to_n as [(_ & ->)| (_ & owner'_to_n)].
          assumption.
        now apply Ok_self; exists owner'.
      Qed.

      Lemma add_eq :
        Ok self ->
        ~ Contains self owner ->
        Ok (Make.add_eq self owner).
      Proof.
        clear color; intros Ok_self not_In_owner.
        split.
          intros color_lt_S_colors.
          apply Lt.lt_n_Sm_le, PeanoNat.Nat.le_lteq in color_lt_S_colors as [color_lt_colors| ->].
            apply Ok_self in color_lt_colors as [owner' owner'_to_color].
            exists owner'.
            now apply Map.add_2;
              [contradict not_In_owner; rewrite not_In_owner; exists color|].
          now exists owner; apply Map.add_1.
        intros [owner' owner'_to_color].
        apply add_mapsto_iff in owner'_to_color as [[eq <-]| [neq owner'_to_color]].
          auto.
        apply PeanoNat.Nat.lt_lt_succ_r, Ok_self.
        now exists owner'.
      Defined.
    End Constructors.
  End Ok.
End Make.

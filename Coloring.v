Require Import Coq.FSets.FMaps.

Module Make (Owner : DecidableType) (Map : WSfun Owner).
  Module Map_Facts := WFacts_fun Owner Map.

  Record t :
    Type :=
    new {
      colors : nat;
      labeling : Map.t nat
    }.

  Notation empty :=
    (new 0 (Map.empty nat))
    (only parsing).

  Notation add_lt
    self
    owner
    color :=
    (new (self.(colors)) (Map.add owner color (self.(labeling))))
    (only parsing).

  Notation add_eq
    self
    owner :=
    (new (S (self.(colors))) (Map.add owner (self.(colors)) (self.(labeling))))
    (only parsing).

  Notation find
    self
    owner :=
    (Map.find owner (self.(labeling)))
    (only parsing).

  Notation MapsTo
    self
    owner
    color :=
    (Map.MapsTo owner color (self.(labeling)))
    (only parsing).

  Notation Contains
    self
    owner :=
    (Map.In owner (self.(labeling)))
    (only parsing).

  Notation Ok
    self :=
    (forall color : nat,
      color < self.(colors) <->
      (exists owner : Owner.t, MapsTo self owner color))
    (only parsing).

  Module Ok.
    Section Constructors.
      Lemma empty :
        Ok Make.empty.
      Proof with auto with arith.
        split.
          intros color_lt_colors.
          contradict color_lt_colors...
        intros [owner owner_to_color].
        contradict owner_to_color.
        firstorder using Map_Facts.empty_in_iff.
      Qed.

      Variables
        (self : Make.t)
        (owner : Owner.t)
        (color : nat).

      Lemma add_lt :
        Ok self ->
        ~ Contains self owner ->
        color < self.(colors) ->
        Ok (Make.add_lt self owner color).
      Proof with auto.
        intros Ok_self not_In_owner color_lt_colors n.
        split.
          intros n_lt_colors.
          apply Ok_self in n_lt_colors as [owner' owner'_to_n].
          exists owner'; apply Map.add_2 with (2 := owner'_to_n).
          contradict not_In_owner.
          rewrite not_In_owner; now exists n.
        intros [owner' owner'_to_n].
        apply Map_Facts.add_mapsto_iff in owner'_to_n as
          [(_ & ->)| (_ & owner'_to_n)]...
        now apply Ok_self; exists owner'.
      Qed.

      Lemma add_eq :
        Ok self ->
        ~ Contains self owner ->
        Ok (Make.add_eq self owner).
      Proof with auto.
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
        apply Map_Facts.add_mapsto_iff in owner'_to_color as
          [[eq <-]| [neq owner'_to_color]]...
        apply PeanoNat.Nat.lt_lt_succ_r, Ok_self.
        now exists owner'.
      Defined.
    End Constructors.
  End Ok.

  Definition eq
    (self other : t) :
    Prop :=
    self.(colors) = other.(colors) /\
    Map.Equal (self.(labeling)) (other.(labeling)).

  Module Eq.
    #[global]
    Instance reflexive :
      Reflexive eq.
    Proof.
      now intros x.
    Qed.

    #[global]
    Instance symmetric :
      Symmetric eq.
    Proof.
      unfold eq.
      intros x y x_eq_y.
      now split; symmetry.
    Qed.

    #[global]
    Instance transitive :
      Transitive eq.
    Proof.
      unfold eq.
      intros x y z x_le_y y_le_z.
      now split;
        [transitivity (y.(colors))| transitivity (y.(labeling))].
    Qed.

    #[global]
    Add Parametric Relation : t eq
      reflexivity proved by reflexive
      symmetry proved by symmetric
      transitivity proved by transitive
      as equivalence.
  End Eq.

  Definition le
    (self other : t) :
    Prop :=
      self.(colors) <= other.(colors) /\
      (forall
        (owner : Owner.t)
        (color : nat),
        MapsTo self owner color ->
        MapsTo other owner color).

  Module Le.
    #[global]
    Instance reflexive :
      Reflexive le.
    Proof.
      now intros x.
    Qed.

    #[global]
    Instance transitive :
      Transitive le.
    Proof.
      unfold le.
      intros x y z x_le_y y_le_z.
      split.
        now transitivity (y.(colors)).
      firstorder.
    Qed.

    #[global]
    Add Parametric Relation : t le
      reflexivity proved by reflexive
      transitivity proved by transitive
      as PreOrder_Le.

    #[global]
    Instance antisymmetric :
      Antisymmetric t eq le.
    Proof with auto with arith.
      unfold le.
      intros x y x_le_y x_ge_y; split.
        destruct x_le_y, x_ge_y...
      intros key.
      destruct (find x key) as [value|] eqn: find; symmetry.
        now apply Map_Facts.find_mapsto_iff, x_le_y, Map_Facts.find_mapsto_iff.
      rewrite <- Map_Facts.not_find_in_iff in find |- *.
      contradict find; destruct find as
        (value & key_to_value).
      now exists value; apply x_ge_y.
    Qed.

    #[global]
    Instance partial_order :
      PartialOrder eq le.
    Proof.
      intros x y.
      split.
        intros (colors_eq & labeling_eq).
        split;
          (now split;
            [rewrite colors_eq| intros owner color; rewrite labeling_eq]).
      intros (x_le_y & x_ge_y).
      now apply antisymmetric.
    Qed.
  End Le.
End Make.

Require Import Coq.MSets.MSets.
Require Import Coq.FSets.FMaps.

Require Import Coq.Arith.Arith.
Require Import Coq.Classes.Morphisms_Prop.

Module Make (Owner : DecidableTypeBoth) (Map : WSfun Owner).
  Module Map_Facts := WFacts_fun Owner Map.
  Module Map_Properties := WProperties_fun Owner Map.

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

  Module Fiber (M : WSetsOn Owner).
    Module M_Facts := MSetFacts.WFactsOn Owner M.
    Module M_Properties := MSetProperties.WPropertiesOn Owner M.

    Section Fiber.
      Variables
        (self : t)
        (y : nat).

      Definition step
        (owner : Owner.t)
        (color : nat)
        (fiber : M.t) :
        M.t :=
        if color =? y then M.add owner fiber else fiber.

      Definition fiber :
        M.t :=
        Map.fold
          step
          self.(labeling)
          M.empty.

      #[global]
      Add Parametric Morphism :
        step with signature
        (Owner.eq ==> eq ==> M.Equal ==> M.Equal) as Proper_step.
      Proof.
        intros p p' p_eq_p' c fiber fiber' fiber_eq_fiber'.
        now unfold step; destruct (c =? y);
          [rewrite p_eq_p'|];
          rewrite fiber_eq_fiber'.
      Qed.

      Lemma transpose_neqkey_step :
        Map_Properties.transpose_neqkey M.Equal step.
      Proof with try reflexivity.
        intros p p' c c' fiber p_neq_p'.
        unfold step.
        destruct (c =? y)...
        destruct (c' =? y)...
        intros owner; rewrite ?M_Facts.add_iff; tauto.
      Qed.

      Lemma spec :
        forall
          owner : Owner.t,
          M.In owner fiber <->
          MapsTo self owner y.
      Proof.
        intros owner.
        unfold fiber, step; destruct self as (colors & labeling).
        apply Map_Properties.fold_rec_weak; clear colors labeling.
            now intros ?labeling labeling' m ->.
          now rewrite Map_Facts.empty_mapsto_iff, M_Facts.empty_iff.
        intros p c fiber labeling not_In_p_labeling IHfiber.
        destruct (Nat.eq_dec c y) as [c_eq_y| c_neq_y].
          assert (c =? y = true) as -> by now apply Nat.eqb_eq.
          rewrite M_Facts.add_iff, IHfiber, Map_Facts.add_mapsto_iff.
          specialize Owner.eq_dec with p owner; firstorder.
        assert (c =? y = false) as -> by now apply Nat.eqb_neq.
        rewrite IHfiber, Map_Facts.add_mapsto_iff.
        enough (Map.MapsTo owner y labeling -> ~ Owner.eq p owner) by
          tauto.
        intros owner_to_y; contradict not_In_p_labeling;
          rewrite not_In_p_labeling.
        now exists y.
      Qed.

      Lemma lt_iff_not_empty :
        Ok self ->
        y < self.(colors) <->
        ~ M.Empty fiber.
      Proof.
        intros Ok_self.
        rewrite Ok_self; split.
          intros (owner & owner_to_y).
          enough (M.In owner fiber) by firstorder.
          now apply spec.
        intros not_Empty_fiber.
        destruct (M.choose fiber) as [owner|] eqn: choose.
          now exists owner; apply spec, M.choose_spec1.
        now contradict not_Empty_fiber; apply M.choose_spec2.
      Qed.

      Lemma ge_iff_empty :
        Ok self ->
        y >= self.(colors) <->
        M.Empty fiber.
      Proof.
        intros Ok_self.
        unfold ge; rewrite Nat.le_ngt, lt_iff_not_empty by assumption.
        now rewrite M_Facts.is_empty_iff, not_true_iff_false, not_false_iff_true.
      Qed.
    End Fiber.

    Section Corollaries.
      Variables
        (self : t)
        (owner : Owner.t).

      Corollary contains_iff :
        Contains self owner <->
        (exists y : nat, M.In owner (fiber self y)).
      Proof.
        symmetry.
        apply ex_iff_morphism; intros y.
        apply spec.
      Qed.

      Corollary not_contains_iff :
        ~ Contains self owner <->
        (forall y : nat, ~ M.In owner (fiber self y)).
      Proof.
        transitivity (~ (exists y : nat, M.In owner (fiber self y))).
          now rewrite contains_iff.
        firstorder.
      Qed.
    End Corollaries.

    Section Constructors.
      Variables
        (self : t)
        (y : nat).

      Lemma empty :
        M.Empty (fiber Make.empty y).
      Proof with auto using Map.empty_1 with set typeclass_instances.
        unfold fiber; simpl; rewrite Map_Properties.fold_Empty...
      Qed.

      Lemma add_lt :
        forall
          (owner : Owner.t)
          (color : nat),
          ~ Contains self owner ->
          (color = y ->
          M_Properties.Add
            owner
            (fiber self y)
            (fiber (Make.add_lt self owner color) y)) /\
          (color <> y ->
          M.Equal
            (fiber (Make.add_lt self owner color) y)
            (fiber self y)).
      Proof with auto using transpose_neqkey_step with typeclass_instances.
        intros owner color not_In_owner.
        unfold fiber at 2 3; simpl; split;
          [intros color_eq_y owner'| intros color_neq_y];
          (rewrite Map_Properties.fold_add; [unfold step at 1|..])...
          apply Nat.eqb_eq in color_eq_y as ->;
            rewrite M.add_spec; firstorder.
          now apply Nat.eqb_neq in color_neq_y as ->.
      Qed.

      Lemma add_eq :
        forall
          owner : Owner.t,
          Ok self ->
          ~ Contains self owner ->
          (self.(colors) = y ->
          M.Equal
            (fiber (Make.add_eq self owner) y)
            (M.singleton owner)) /\
          (self.(colors) <> y ->
          M.Equal
            (fiber (Make.add_eq self owner) y)
            (fiber self y)).
      Proof with auto using transpose_neqkey_step with typeclass_instances.
        intros owner Ok_self not_In_owner.
        split.
          intros colors_eq_y.
          transitivity (M.add owner (fiber self y)).
            rewrite <- M_Properties.Add_Equal; simpl.
            now apply add_lt.
          rewrite M_Properties.empty_is_empty_1 with (s := fiber self y).
            intros owner'; M_Facts.set_iff; tauto.
          apply ge_iff_empty;
            [| rewrite colors_eq_y];
            auto with arith.
        now apply add_lt.
      Qed.
    End Constructors.
  End Fiber.

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

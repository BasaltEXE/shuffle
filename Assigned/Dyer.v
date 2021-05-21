Set Implicit Arguments.
Set Printing Projections.

Require Import Coq.Structures.Equalities Coq.Structures.EqualitiesFacts.
Require Import Coq.Structures.Orders Coq.Structures.OrdersFacts.

Require Import Coq.Lists.SetoidList.
Import ListNotations.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Classes.RelationClasses.

Require Import Coq.Arith.Arith.

Require Coq.MSets.MSets.
Require Coq.FSets.FMaps.

Require Import Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Require Import Setoid.

Require Import Shuffle.Misc.
Require Import Shuffle.List.

Require Import Shuffle.Relations.

Require Shuffle.Assigned.Instructions.
Require Import Shuffle.Coloring.

Module WFacts_fun' (Key : DecidableTypeOrig) (Map : FMapInterface.WSfun Key).
  Include FMapFacts.WFacts_fun Key Map. (* TODO *)

  Lemma find_spec : forall
    [elt : Type]
    (m : Map.t elt)
    (x : Map.key),
    OptionSpec
      (fun e : elt => Map.MapsTo x e m)
      (~ Map.In x m)
      (Map.find x m).
  Proof.
    intros elt m x.
    destruct (Map.find x m) eqn: find; constructor.
      now apply find_mapsto_iff.
    now apply not_find_in_iff.
  Qed.

  Lemma find_In_Some : forall
    [elt : Type]
    (m : Map.t elt)
    (x : Map.key),
    Map.In x m ->
    exists e : elt,
      Map.find x m = Some e /\
      Map.MapsTo x e m.
  Proof.
    intros elt m x m_in_x.
    destruct (Map.find x m) as [e|] eqn: find.
      exists e.
      now split; [| apply find_mapsto_iff].
    now contradict find; apply in_find_iff.
  Qed.

  Lemma add_eq_mapsto_iff : forall
    [elt : Type]
    (m : Map.t elt)
    (x y : Map.key)
    (e e' : elt),
    Key.eq x y ->
      Map.MapsTo y e' (Map.add x e m) <->
      e = e'.
  Proof.
    intros; rewrite add_mapsto_iff; tauto.
  Qed.

  Lemma add_not_in_iff : forall
    [elt : Type]
    (m : Map.t elt)
    (x y : Map.key)
    (e : elt),
    ~ Map.In y (Map.add x e m) <->
      ~ Key.eq x y /\
      ~ Map.In y m.
  Proof.
    intros elt m x y e.
    rewrite add_in_iff; tauto.
  Qed.

  Lemma add_not_in : forall
    [elt : Type]
    (m : Map.t elt)
    (x y : Map.key)
    (e : elt),
    ~ Key.eq x y ->
    ~ Map.In y m ->
    ~ Map.In y (Map.add x e m).
  Proof.
    intros elt m x y e.
    rewrite add_in_iff; tauto.
  Qed.
End WFacts_fun'.

Module Type LabelledTransitionSystem.
  Parameter State : Type.
  Parameter Label : Type.
  Parameter Transition : Label -> relation State.
End LabelledTransitionSystem.

Module Graph (Import LTS : LabelledTransitionSystem).
  Inductive t :
    list Label ->
    relation State :=
    | nil :
      forall
      p : State,
      t [] p p
    | cons :
      forall
      (p₀ p₁ q : State)
      (u₀ : Label)
      (x₀ : list Label),
      Transition u₀ p₀ p₁ ->
      t x₀ p₁ q ->
      t (u₀ :: x₀) p₀ q.
End Graph.

Module Make (Owner : DecidableTypeBoth) (Map : FMapInterface.WSfun Owner).
  Module Coloring := Coloring.Make Owner Map.

  Module Import Instructions := Instructions.Make Owner.
  Import Instructions.Notations.

  Module Import Facts := WFacts_fun' Owner Map.

  Ltac split_left :=
    split; [| try split_left].

  Import Instructions.Ok.
  Import Instructions.Hints.

  Module Regular.
    Fixpoint regular_body
      (instructions : list Instruction.t)
      (coloring : Coloring.t)
      (unused_colors : list nat) :
      option (Coloring.t * list nat) :=
      match instructions, unused_colors with
      | Up owner :: tail, [] =>
        regular_body
          tail
          (Coloring.add_eq coloring owner)
          []
      | Up owner :: tail, color :: unused_colors =>
        regular_body
          tail
          (Coloring.add_lt coloring owner color)
          unused_colors
      | Down owner :: tail, unused_colors =>
          bind (Coloring.find coloring owner) (fun color =>
          regular_body
            tail
            coloring
            (color :: unused_colors))
      | [], _ => ret (coloring, unused_colors)
      end.

    Definition regular
      (instructions : list Instruction.t) :
      option Coloring.t :=
      bind (regular_body
        instructions
        Coloring.empty
        []) (fun x => Some (fst x)).

    Module State.
      Record t :
        Type :=
        new {
          coloring : Coloring.t;
          unused_colors : list nat;
        }.

      Notation initial_state :=
        {|
          coloring := Coloring.empty;
          unused_colors := [];
        |}.

      Module Ok.
        Notation Active_MapsTo
          xs
          owner
          color
          :=
          (Active owner (fst xs) /\
          Coloring.MapsTo (snd xs).(State.coloring) owner color).

        Module M := MSetWeakList.Make Owner.
        Module Fiber := Coloring.Fiber M.
        Module Sets := Instructions.Active.Sets M.

        Definition Active_MapsTo_dec :
          forall
          (x : Instructions.t)
          (s : State.t)
          (color : nat),
          Instructions.Ok x ->
          (exists owner : Owner.t, State.Ok.Active_MapsTo (x, s) owner color) +
          (forall owner : Owner.t, ~ State.Ok.Active_MapsTo (x, s) owner color).
        Proof.
          intros x s color Ok_x.
          pose (fiber := Fiber.fiber s.(State.coloring) color).
          pose (active := Sets.active x).
          pose (inter := M.inter fiber active).
          assert (inter_iff : forall p, M.In p inter <-> State.Ok.Active_MapsTo (x, s) p color).
            intros p.
            unfold inter; rewrite M.inter_spec, <- Fiber.spec, <- Sets.spec; tauto.
          destruct (M.choose inter) as [owner|] eqn: choose; [left| right].
            now exists owner; apply inter_iff, M.choose_spec1.
          now intros owner; rewrite <- inter_iff; apply M.choose_spec2.
        Defined.

        Record t
          (x : Instructions.t)
          (s : State.t) :
          Prop :=
          new {
            coloring :
              Coloring.Ok s.(State.coloring);
            ahead :
              forall
              owner : Owner.t,
              Ahead owner x ->
              ~ Map.In owner s.(State.coloring).(Coloring.labeling);
            active :
              forall
              owner : Owner.t,
              Active owner x ->
              Map.In owner s.(State.coloring).(Coloring.labeling);
            proper :
              forall
              (owner owner' : Owner.t)
              (color : nat),
              Active_MapsTo (x, s) owner color ->
              Active_MapsTo (x, s) owner' color ->
              Owner.eq owner owner';
            unused :
              forall
              color : nat,
              List.In color s.(State.unused_colors) <->
              color < s.(State.coloring).(Coloring.colors) /\
              (forall
              owner : Owner.t,
              ~ Active_MapsTo (x, s) owner color);
            nodup :
              NoDup s.(State.unused_colors);
          }.

        Lemma InA_eq_iff_In :
          forall
          (A : Type)
          (a : A)
          (l : list A),
          InA eq a l <-> List.In a l.
        Proof.
          intros A a l.
          rewrite InA_alt.
          split.
            now intros (y & -> & In_y_l).
          now intros In_a_l; exists a.
        Qed.

        Lemma NoDupA_eq_iff_NoDup :
          forall
          (A : Type)
          (l : list A),
          NoDupA eq l <-> NoDup l.
        Proof.
          induction l as [| h t IHt].
            split; constructor.
          rewrite NoDup_cons_iff.
          transitivity (~ InA eq h t /\ NoDupA eq t).
            now split; [inversion 1| constructor].
          now rewrite InA_eq_iff_In, IHt.
        Qed.

        Module N := MSetWeakList.Make Nat.
        Module N_Properties := MSetProperties.WProperties N.

        Lemma active_plus_unused :
          forall
          (x : Instructions.t)
          (s : State.t),
          Instructions.Ok x ->
          State.Ok.t x s ->
          s.(State.coloring).(Coloring.colors) =
            Sets.count x +
            length s.(State.unused_colors).
        Proof.
          intros x s Ok_x Ok_s.
          set (colors := s.(State.coloring).(Coloring.colors)).
          assert (exists p : N.t, N.cardinal p = colors /\ forall color : nat, N.In color p <-> color < colors) as
            (p & length_p & p_In_iff).
            eexists {|
              N.this := seq 0 colors;
              N.is_ok := ?[ok]
            |}; split.
                only [ok]: (apply NoDupA_eq_iff_NoDup, seq_NoDup).
              apply seq_length.
            intros color; change (InA eq color (seq 0 colors) <-> color < colors).
            rewrite InA_eq_iff_In, in_seq.
            firstorder with arith.
          assert (exists r : N.t, N.cardinal r = length s.(State.unused_colors) /\ forall color : nat, N.In color r <-> color < colors /\ forall owner : Owner.t, ~ State.Ok.Active_MapsTo (x, s) owner color) as
            (r & <- & r_In_iff).
            eexists {|
              N.this := s.(State.unused_colors);
              N.is_ok := ?[ok]
            |}.
              only [ok]: (apply NoDupA_eq_iff_NoDup, Ok_s.(State.Ok.nodup)).
            split.
              reflexivity.
            intros color.
            transitivity (List.In color s.(State.unused_colors)).
              now rewrite <- InA_eq_iff_In.
            apply Ok_s.(State.Ok.unused).
          assert (exists q : N.t, N.cardinal q = M.cardinal (Sets.active x) /\ forall color : nat, N.In color q <-> color < s.(State.coloring).(Coloring.colors) /\ exists owner : Owner.t, M.In owner (Sets.active x) /\ State.Ok.Active_MapsTo (x, s) owner color) as (q & <- & q_In_iff).
            cut (forall owner, M.In owner (Sets.active x) -> Active owner x).
              2: now intros owner; apply Sets.spec.
            destruct (Sets.active x) as (l & NoDup_l).
            induction l as [| h t IHt]; intros H.
              eexists {|
                N.this := [];
                N.is_ok := ?[ok];
              |}.
                only [ok]: constructor.
              split.
                reflexivity.
              intros color; split.
                now intros In_color_q; apply InA_nil in In_color_q.
              intros (_ & owner & color_in_q & _).
              now apply InA_nil in color_in_q.
            inversion_clear NoDup_l as [| ? ? not_In_h_t NoDup_t].
            specialize IHt with NoDup_t as ((q₀ & NoDup_q₀) & q₀_eq_t & q₀_in_iff).
              intros owner In_owner_t.
              now apply H; constructor 2.
            assert (exists color, color < s.(State.coloring).(Coloring.colors) /\ Coloring.MapsTo s.(State.coloring) h color) as (color & color_lt_colors & h_to_color).
              assert (Active_h : Active h x) by (now apply H; constructor).
              specialize Ok_s.(State.Ok.active) with (1 := Active_h) as (color & h_to_color).
              now exists color; split;
              [apply Ok_s.(State.Ok.coloring); exists h|].
            eexists {|
              N.this := color :: q₀;
              N.is_ok := ?[ok];
            |}.
            split.
              change (S (length q₀) = S (length t)).
              now f_equal.
            intros color'.
            unfold N.In, N.Raw.In, M.In, M.Raw.In in q₀_in_iff |- *;
            simpl in q₀_in_iff |- *; setoid_rewrite InA_cons.
            enough (color' = color <-> color' < s.(State.coloring).(Coloring.colors) /\ exists owner : Owner.t, Owner.eq owner h /\
            Active owner x /\
            Map.MapsTo owner color' s.(State.coloring).(Coloring.labeling)) as ->.
              rewrite q₀_in_iff;
              firstorder.
            split.
              enough (Active_h : Active h x) by
                (now intros ->; split; [| exists h]).
              now apply H; constructor.
            intros (_ & owner & -> & _ & h_to_color').
            now apply Facts.MapsTo_fun with (1 := h_to_color').
          Unshelve.
          2: {
            constructor; [| assumption].
            unfold N.In, N.Raw.In in q₀_in_iff; simpl in q₀_in_iff.
            rewrite q₀_in_iff.
            enough (forall owner : Owner.t, State.Ok.Active_MapsTo (x, s) owner color -> ~ InA Owner.eq owner t) by firstorder.
            simpl; intros owner Active_MapsTo_owner_color.
            enough (Owner.eq h owner) as <- by assumption.
            apply Ok_s.(State.Ok.proper) with (2 := Active_MapsTo_owner_color).
            now split; [apply H; constructor|].
          }
          rewrite <- N_Properties.union_cardinal, <- length_p by firstorder.
          apply N_Properties.Equal_cardinal.
          intros color.
          rewrite N.union_spec, p_In_iff, q_In_iff, r_In_iff.
          unfold colors.
          split; [simpl| tauto].
          intros color_lt_colors.
          now specialize (Active_MapsTo_dec s color Ok_x) as [
            (owner & Active_MapsTo_owner_color)|
          H];
          [left; split; [| exists owner; rewrite Sets.spec]| right].
        Qed.

        Ltac Ok_tac :=
          simpl in *; eauto using Nat.lt_neq with arith instructions map.

        Module Empty.
          Section Empty.
            Variable
              x : Instructions.t.

            Let s :
              State.t :=
              {|
                State.coloring := Coloring.empty;
                State.unused_colors := [];
              |}.

            Lemma Ok :
              Instructions.Ok x ->
              Instructions.Closed x ->
              State.Ok.t x s.
            Proof.
              intros Ok_x Closed_x.
              specialize Closed_impl_not_Active with
                (1 := Closed_x) as
                not_Active.
              constructor.
                        apply Coloring.Ok.empty.
                      intros owner Ahead_owner_x.
                      specialize Map.empty_1 with nat; firstorder.
                    intros owner Active_owner_x.
                    now contradict Active_owner_x.
                  intros owner owner' color (Active_owner_x & _);
                  now contradict Active_owner_x.
                intros color.
                specialize Nat.nlt_0_r with color; simpl; tauto.
              constructor.
            Qed.
          End Empty.
        End Empty.

        Module UpNil.
          Section UpNil.
            Variables
              (p₀ : Owner.t)
              (x₀ : Instructions.t)
              (coloring : Coloring.t).

            Let s₀ :
              State.t :=
              {|
                State.coloring := coloring;
                State.unused_colors := [];
              |}.

            Let s₁ :
              State.t :=
              {|
                State.coloring := Coloring.add_eq coloring p₀;
                State.unused_colors := [];
              |}.

            Variable instructions₀ :
              Instructions.Ok (Up p₀ :: x₀).
            Variable Ok_s₀ :
              Ok.t (Up p₀ :: x₀) s₀.

            Lemma Active_MapsTo_iff :
              forall
              (color : nat)
              (owner : Owner.t),
              Active_MapsTo (x₀, s₁) owner color <->
              (color = s₀.(State.coloring).(Coloring.colors) /\
              Owner.eq p₀ owner) \/
              (color <> s₀.(State.coloring).(Coloring.colors) /\
              Active_MapsTo (Up p₀ :: x₀, s₀) owner color). (* TODO /\ p₀ <> owner? *)
            Proof with Ok_tac.
              intros color owner.
              enough (H₁ : Owner.eq p₀ owner -> Active owner x₀).
                enough (H₂ : Coloring.MapsTo coloring owner color -> color <> coloring.(Coloring.colors)).
                  simpl; rewrite add_mapsto_iff, Instructions.Active.cons_Up_iff.
                  setoid_replace (coloring.(Coloring.colors) = color) with
                    (color = coloring.(Coloring.colors)) by easy.
                  tauto.
                intros owner_to_color.
                now apply Nat.lt_neq, Ok_s₀.(State.Ok.coloring); exists owner.
              intros <-...
            Qed.

            Lemma Ok :
              Ok.t x₀ s₁.
            Proof with Ok_tac.
              constructor.
                        apply Coloring.Ok.add_eq.
                          apply Ok_s₀.(Ok.coloring).
                        apply Ok_s₀.(Ok.ahead)...
                      intros owner Ahead_owner_x₀.
                      simpl; rewrite add_neq_in_iff.
                        apply Ok_s₀.(Ok.ahead)...
                      contradict Ahead_owner_x₀; rewrite <- Ahead_owner_x₀...
                    intros owner Active_owner_x₀.
                    simpl; rewrite add_in_iff;
                    specialize Owner.eq_dec with p₀ owner as
                      [<-|
                    p₀_neq_owner];
                      [left|
                    right]...
                    apply Ok_s₀.(Ok.active)...
                  setoid_rewrite Active_MapsTo_iff.
                  intros owner owner' color Active_MapsTo_owner_color Active_MapsTo_owner'_color.
                  specialize Nat.eq_dec with color coloring.(Coloring.colors) as
                    [color_eq_colors|
                  color_neq_colors].
                    transitivity p₀; [symmetry|]; tauto.
                  apply Ok_s₀.(Ok.proper) with color; tauto.
                intros color.
                etransitivity; [apply Ok_s₀.(Ok.unused)|].
                setoid_replace (color < s₁.(State.coloring).(Coloring.colors)) with (color < coloring.(Coloring.colors) \/ color = coloring.(Coloring.colors)) by now rewrite <- Nat.le_lteq, Nat.succ_le_mono.
                setoid_replace (forall owner : Owner.t, ~ Active_MapsTo (x₀, s₁) owner color) with (color <> coloring.(Coloring.colors) /\ forall owner, ~ Active_MapsTo (Up p₀ :: x₀, s₀) owner color).
                  firstorder.
                setoid_rewrite Active_MapsTo_iff;
                specialize Nat.eq_dec with color coloring.(Coloring.colors);
                firstorder.
              constructor.
            Qed.
          End UpNil.
        End UpNil.

        Module UpCons.
          Section UpCons.
            Variables
              (p₀ : Owner.t)
              (x₀ : Instructions.t)
              (coloring : Coloring.t)
              (unused_color : nat)
              (unused_colors : list nat).

            Let s₀ :
              State.t :=
              {|
                State.coloring := coloring;
                State.unused_colors := unused_color :: unused_colors;
              |}.

            Let s₁ :
              State.t :=
              {|
                State.coloring := Coloring.add_lt coloring p₀ unused_color;
                State.unused_colors := unused_colors;
              |}.

            Variable Ok_s₀ :
              Ok.t (Up p₀ :: x₀) s₀.
            Variable instructions₀ :
              Instructions.Ok (Up p₀ :: x₀).

            Lemma Active_MapsTo_iff :
              forall
              (color : nat)
              (owner : Owner.t),
              Active_MapsTo (x₀, s₁) owner color <->
              (color = unused_color /\
              Owner.eq p₀ owner) \/
              (color <> unused_color /\
              Active_MapsTo (Up p₀ :: x₀, s₀) owner color).
            Proof with Ok_tac.
              intros color owner.
              enough (H₁ : Owner.eq p₀ owner -> Active owner x₀).
                enough (H₂ : Active owner x₀ -> ~ Owner.eq p₀ owner -> Map.MapsTo owner color coloring.(Coloring.labeling) -> color <> unused_color).
                  simpl; rewrite Instructions.Active.cons_Up_iff, add_mapsto_iff.
                  setoid_replace (unused_color = color) with
                    (color = unused_color) by easy.
                  tauto.
                enough (color = unused_color -> ~ Active_MapsTo (Up p₀ :: x₀, s₀) owner color) by
                  (simpl in H; rewrite Active.cons_Up_iff in H; tauto).
                now intros ->; apply Ok_s₀.(State.Ok.unused); left.
              intros <-...
            Qed.

            Lemma Ok :
              Ok.t x₀ s₁.
            Proof with Ok_tac.
              constructor.
                        apply Coloring.Ok.add_lt.
                            apply Ok_s₀.(Ok.coloring).
                          apply Ok_s₀.(Ok.ahead)...
                        now apply Ok_s₀.(Ok.unused); left.
                      intros owner Ahead_owner_x₀.
                      simpl; rewrite add_neq_in_iff.
                        apply Ok_s₀.(Ok.ahead)...
                      contradict Ahead_owner_x₀; rewrite <- Ahead_owner_x₀...
                    intros owner Active_owner_x₀.
                    apply add_in_iff; specialize Owner.eq_dec with p₀ owner as
                      [p₀_eq_owner|
                    p₀_neq_owner];
                      [left|
                    right; apply Ok_s₀.(Ok.active)]...
                  setoid_rewrite Active_MapsTo_iff.
                  intros owner owner' color Active_Maps_To_owner_color Active_MapsTo_owner_color'.

                  specialize Nat.eq_dec with color unused_color as
                    [color_eq_colors|
                  color_neq_colors].
                    transitivity p₀; [symmetry|]; tauto.
                  apply Ok_s₀.(Ok.proper) with color; tauto.
                intros color.
                transitivity (color <> unused_color /\ List.In color s₀.(State.unused_colors)).
                  setoid_replace (color <> unused_color) with (unused_color <> color) by intuition.
                  enough (List.In color s₁.(State.unused_colors) -> color <> unused_color).
                    simpl; intuition.
                  intros In_color_unused_colors;
                  contradict In_color_unused_colors;
                  rewrite In_color_unused_colors.
                  apply NoDup_cons_iff, Ok_s₀.(Ok.nodup).
                rewrite Ok_s₀.(Ok.unused).
                setoid_replace (forall owner : Owner.t, ~ Active_MapsTo (x₀, s₁) owner color) with (color <> unused_color /\ forall owner, ~ Active_MapsTo (Up p₀ :: x₀, s₀) owner color).
                  tauto.
                setoid_rewrite Active_MapsTo_iff.
                specialize Nat.eq_dec with color unused_color;
                firstorder.
              apply NoDup_cons_iff with unused_color, Ok_s₀.(Ok.nodup).
            Qed.
          End UpCons.
        End UpCons.

        Module Down.
          Section Down.
            Variables
              (p₀ : Owner.t)
              (x₀ : Instructions.t)
              (coloring : Coloring.t)
              (used_color : nat)
              (unused_colors : list nat)
              (p₀_to_used_color : Coloring.MapsTo coloring p₀ used_color).

            Let s₀ :
              State.t :=
              {|
                State.coloring := coloring;
                State.unused_colors := unused_colors;
              |}.

            Let s₁ :
              State.t :=
              {|
                State.coloring := coloring;
                State.unused_colors := used_color :: unused_colors;
              |}.

            Variable Ok_s₀ :
              Ok.t (Down p₀ :: x₀) s₀.
            Variable instructions₀ :
              Instructions.Ok (Down p₀ :: x₀).

            Lemma Active_MapsTo_iff :
              forall
              (color : nat)
              (owner : Owner.t),
              Active_MapsTo (x₀, s₁) owner color <->
              color <> used_color /\ Active_MapsTo (Down p₀ :: x₀, s₀) owner color.
            Proof with Ok_tac.
              intros color owner.
              enough (H₁ : Owner.eq p₀ owner -> Coloring.MapsTo coloring owner color -> color = used_color).
                enough (H₂ : Active owner x₀ -> Coloring.MapsTo coloring owner color -> color <> used_color).
                  simpl; rewrite Active.cons_Down_iff; tauto.
                intros Active_owner owner_to_color.
                enough (p₀_neq_owner : ~ Owner.eq p₀ owner).
                  contradict p₀_neq_owner;
                  rewrite p₀_neq_owner in owner_to_color.
                  apply Ok_s₀.(State.Ok.proper) with used_color...
                contradict Active_owner; rewrite <- Active_owner...
              intros <- p₀_to_color.
              now apply Facts.MapsTo_fun with coloring.(Coloring.labeling) p₀.
            Qed.

            Lemma Ok :
              Ok.t x₀ s₁.
            Proof with Ok_tac.
              constructor.
                        apply Ok_s₀.(Ok.coloring).
                        intros owner Ahead_owner_x₀.
                      apply Ok_s₀.(Ok.ahead)...
                    intros owner Active_owner_x₀.
                    apply Ok_s₀.(Ok.active)...
                  setoid_rewrite Active_MapsTo_iff.
                  intros owner owner' color
                    Active_MapsTo_owner_color Active_MapsTo_owner'_color.
                  now apply Ok_s₀.(Ok.proper) with color.
                intros color.
                setoid_rewrite Active_MapsTo_iff.
                transitivity (color = used_color \/ List.In color s₀.(State.unused_colors)).
                  simpl; intuition.
                rewrite Ok_s₀.(Ok.unused).
                setoid_replace ((forall owner : Owner.t,
                ~ (color <> used_color /\ Active_MapsTo (Down p₀ :: x₀, s₀) owner color))) with (color = used_color \/ (forall owner, ~ Active_MapsTo (Down p₀ :: x₀, s₀) owner color)).
                  enough (used_color < coloring.(Coloring.colors)) by
                    (simpl; intuition).
                  apply Ok_s₀.(Ok.coloring); exists p₀...
                specialize Nat.eq_dec with color used_color;
                firstorder.
              constructor.
                change (~ List.In used_color s₀.(State.unused_colors)).
                rewrite Ok_s₀.(Ok.unused).
                enough (Active_MapsTo (Down p₀ :: x₀, s₀) p₀ used_color).
                  firstorder.
                split...
              apply Ok_s₀.(Ok.nodup).
            Qed.
          End Down.
        End Down.
      End Ok.
      Import Ok(Active_MapsTo).

      Module Transition.
        Inductive t :
          Instruction.t ->
          relation State.t :=
          | UpNil :
            forall
            (p₀ : Owner.t)
            (coloring : Coloring.t),
            t
              (Up p₀)
              {|
                coloring := coloring;
                unused_colors := []
              |}
              {|
                coloring := Coloring.add_eq coloring p₀;
                unused_colors := []
              |}
          | UpCons :
            forall
            (p₀ : Owner.t)
            (coloring : Coloring.t)
            (unused_color : nat)
            (unused_colors : list nat),
            t
              (Up p₀)
              {|
                coloring := coloring;
                unused_colors := unused_color :: unused_colors
              |}
              {|
                coloring := Coloring.add_lt coloring p₀ unused_color;
                unused_colors := unused_colors
              |}
          | Down :
            forall
            (p₀ : Owner.t)
            (coloring : Coloring.t)
            (used_color : nat)
            (unused_colors : list nat),
            Coloring.MapsTo coloring p₀ used_color ->
            t
              (Down p₀)
              {|
                coloring := coloring;
                unused_colors := unused_colors
              |}
              {|
                coloring := coloring;
                unused_colors := used_color :: unused_colors
              |}.

        Instance functional (u₀ : Instruction.t) :
          Functional (t u₀).
        Proof.
          intros s t t' Transition_s_t Transition_s_t'.
          induction Transition_s_t as [
              p₀ coloring|
            p₀ coloring unused_color unused_colors|
          p₀ coloring used_color unused_colors p₀_to_used_color];
          inversion_clear Transition_s_t' as [
              |
            |
          ? ? used_color' ? p_to_used_color'];
          [reflexivity..|].
          enough (used_color = used_color') as -> by reflexivity.
          now apply MapsTo_fun with coloring.(Coloring.labeling) p₀.
        Qed.

        Definition serial :
          forall
          (u₀ : Instruction.t)
          (x₀ : Instructions.t)
          (s₀ : State.t),
          Instructions.Ok (u₀ :: x₀) ->
          State.Ok.t (u₀ :: x₀) s₀ ->
          exists s₁ : State.t,
          Transition.t u₀ s₀ s₁.
        Proof.
          intros ([|] & p₀) x₀ (coloring & unused_colors) Ok_x Ok_s₀.
            destruct unused_colors as [| unused_color unused_colors].
              exists {|
                coloring := Coloring.add_eq coloring p₀;
                unused_colors := []
              |}; constructor.
            exists {|
              coloring := Coloring.add_lt coloring p₀ unused_color;
              unused_colors := unused_colors
            |}; constructor.
          enough (Map.In p₀ coloring.(Coloring.labeling)) as (used_color & p₀_to_used_color).
            now exists {|
              coloring := coloring;
              unused_colors := used_color :: unused_colors;
            |}; constructor.
          apply Ok_s₀.(Ok.active); auto with instructions.
        Qed.

        Definition Ok_morphism :
          forall
          (u₀ : Instruction.t)
          (x₀ : Instructions.t)
          (s₀ s₁ : State.t),
          Instructions.Ok (u₀ :: x₀) ->
          Transition.t u₀ s₀ s₁ ->
          State.Ok.t (u₀ :: x₀) s₀ ->
          State.Ok.t x₀ s₁.
        Proof.
          intros u₀ x₀ s₀ s₁ Ok_x Transition_s₀_s₁ Ok_s₀.
          induction Transition_s₀_s₁ as [
              p₀ coloring|
            p₀ coloring unused_color unused_colors|
          p₀ coloring used_color unused_colors p₀_to_used_color].
              now apply State.Ok.UpNil.Ok.
            now apply State.Ok.UpCons.Ok.
          now apply State.Ok.Down.Ok with (1 := p₀_to_used_color).
        Qed.

        Lemma coloring_morphism :
          forall
          (u₀ : Instruction.t)
          (x₀ : Instructions.t)
          (s₀ s₁ : State.t),
          Instructions.Ok (u₀ :: x₀) ->
          State.Ok.t (u₀ :: x₀) s₀ ->
          Transition.t u₀ s₀ s₁ ->
          Coloring.le s₀.(State.coloring) s₁.(State.coloring).
        Proof with State.Ok.Ok_tac.
          intros u₀ x₀ s₀ s₁ Ok_x Ok_s₀ Transition_s₀_s₁.
          induction Transition_s₀_s₁ as [
              p₀ coloring|
            p₀ coloring unused_color unused_colors|
          p₀ coloring used_color unused_colors p₀_to_used_color].
            1, 2:
              split;
                [auto with arith|
              intros owner color owner_to_color;
              enough (~ Owner.eq p₀ owner)]...
            1, 2:
              contradict owner_to_color; rewrite <- owner_to_color;
              enough (~ Map.In p₀ coloring.(Coloring.labeling)) by firstorder;
              apply Ok_s₀.(State.Ok.ahead)...
          reflexivity.
        Qed.
      End Transition.

      Module Graph.
        Inductive t :
          Instructions.t ->
          relation State.t :=
        | Nil :
          forall
          s : State.t,
          t [] s s
        | Cons :
          forall
          (u₀ : Instruction.t)
          (x₀ : Instructions.t)
          (s₀ s₁ u : State.t),
          Transition.t u₀ s₀ s₁ ->
          t x₀ s₁ u ->
          t (u₀ :: x₀) s₀ u.

        Lemma nil_iff :
          forall
          (s t : State.t),
          Graph.t [] s t <->
          s = t.
        Proof.
          intros s t; split.
            now inversion 1.
          intros <-; constructor 1.
        Qed.

        Lemma cons_iff :
          forall
          (u₀ : Instruction.t)
          (x₀ : Instructions.t)
          (s₀ t : State.t),
          Graph.t (u₀ :: x₀) s₀ t <->
          exists
          s₁ : State.t,
          Transition.t u₀ s₀ s₁ /\
          Graph.t x₀ s₁ t.
        Proof.
          intros u₀ x₀ s₀ t; split.
            inversion 1; firstorder.
          intros (s₁ & Transition_s₀_s₁ & Graph_s₁_t₁).
          now constructor 2 with s₁.
        Qed.

        Instance functional (x : Instructions.t) :
          Functional (t x).
        Proof.
          intros s t t' Graph_s_t Graph_s_t'.
          induction Graph_s_t as [
            s|
          u₀ x₀ s₀ s₁ t Transition_s₀_s₁ Graph_s₁_t IHGraph_s₁_t];
          inversion_clear Graph_s_t' as [
            |
          ? ? ? s₁' ? Transition_s₀_s₁' Graph_s₁_t'].
            reflexivity.
          enough (s₁ = s₁') as <- by now apply IHGraph_s₁_t.
          now apply Transition.functional with (1 := Transition_s₀_s₁).
        Qed.

        Lemma serial :
          forall
          (x : Instructions.t)
          (s : State.t),
          Instructions.Ok x ->
          State.Ok.t x s ->
          exists
          t : State.t,
          Graph.t x s t.
        Proof.
          intros x.
          induction x as [| u₀ x₀ IHx₀].
            intros s; exists s; constructor.
          intros s₀ Ok_x Ok_s₀.
          specialize State.Transition.serial with (1 := Ok_x) (2 := Ok_s₀) as (s₁ & Transition_s₀_s₁).
          specialize IHx₀ with s₁ as (t & Graph_s₁_t).
              eauto with instructions.
            now apply State.Transition.Ok_morphism with u₀ s₀.
          now exists t; apply Graph.Cons with s₁.
        Qed.

        Lemma Ok_morphism :
          forall
          (x y : Instructions.t)
          (s t : State.t),
          Instructions.Ok (x ++ y) ->
          State.Ok.t (x ++ y) s ->
          Graph.t x s t ->
          State.Ok.t y t.
        Proof with State.Ok.Ok_tac.
          induction x as [| u₀ x₀ IHx₀]; intros y s t Ok_x Ok_s Graph_s_t.
            now apply nil_iff in Graph_s_t as <-.
          apply cons_iff in Graph_s_t as (s' & Transition_s_s' & Graph_s'_t).
          apply (@IHx₀ y s' t).
              eauto with instructions.
            now apply State.Transition.Ok_morphism with (2 := Transition_s_s').
          assumption.
        Qed.

        Lemma coloring_morphism :
          forall
          (x : Instructions.t)
          (s t : State.t),
          Instructions.Ok x ->
          State.Ok.t x s ->
          Graph.t x s t ->
          Coloring.le s.(State.coloring) t.(State.coloring).
        Proof with State.Ok.Ok_tac.
          intros x s t Ok_x Ok_s Graph_s_t.
          induction Graph_s_t as [
            s|
          u₀ x₀ s₀ s₁ t Transition_s₀_s₁ Graph_s₁_t IHs₁_t].
            reflexivity.
          transitivity s₁.(State.coloring).
            now apply (@State.Transition.coloring_morphism u₀ x₀ s₀ s₁).
          apply IHs₁_t...
          now apply (@State.Transition.Ok_morphism u₀ x₀ s₀).
        Qed.

        Lemma Active_MapsTo_iff :
          forall
          (x : Instructions.t)
          (s t : State.t),
          Instructions.Ok x ->
          Graph.t x s t ->
          State.Ok.t x s ->
          forall
          (owner : Owner.t)
          (color : nat),
          Active owner x ->
          Coloring.MapsTo s.(State.coloring) owner color <->
          Coloring.MapsTo t.(State.coloring) owner color.
        Proof.
          intros x s t Ok_x Graph_s_t Ok_s owner color Active_owner_s.
          assert (s_le_t : Coloring.le s.(State.coloring) t.(State.coloring)) by
            now apply coloring_morphism with (3 := Graph_s_t).
          split.
            apply s_le_t.
          intros owner_to_color_t.
          specialize Ok_s.(State.Ok.active) with (1 := Active_owner_s) as
            (color' & owner_to_color'_s).
          enough (color = color') as -> by assumption.
          apply MapsTo_fun with (1 := owner_to_color_t).
          now apply s_le_t.
        Qed.

        Lemma split :
          forall
          (x : Instructions.t)
          (s t : State.t),
          Graph.t x s t ->
          forall
          left right : Instructions.t,
          left ++ right = x ->
          exists
          s' : State.t,
          Graph.t left s s' /\ Graph.t right s' t.
        Proof.
          intros x s t Graph_s_t.
          induction Graph_s_t as [
            s|
          u₀ x₀ s₀ s₁ t Transition_s₀_s₁ Graph_s₁_t IHs₁_t].
            intros left right H; apply app_eq_nil in H as (-> & ->).
            exists s; split; constructor.
          intros [| head_left tail_left] right H.
            exists s₀; split.
              constructor.
            simpl in H.
            rewrite H.
            now apply Graph.Cons with s₁.
          simpl in H.
          inversion H.
          specialize IHs₁_t with (1 := H2) as (s' & Graph_s₁_s' & Graph_s'_t).
          exists s'; split.
            now apply Graph.Cons with s₁.
          assumption.
        Qed.
      End Graph.
    End State.
    Module Sets := State.Ok.Sets.
    Module Graph := State.Graph.

    Lemma regular_body_spec :
      forall
      (x : Instructions.t)
      (s t : State.t),
      Graph.t x s t ->
      regular_body x s.(State.coloring) s.(State.unused_colors) =
      Some (t.(State.coloring), t.(State.unused_colors)).
    Proof.
      intros x s t Graph_s_t.
      induction Graph_s_t as [
        s|
      u₀ x₀ s₀ s₁ t Transition_s₀_s₁ Graph_s₁_t IHGraph_s₁_t].
        reflexivity.
      induction Transition_s₀_s₁ as [
          p₀ coloring|
        p₀ coloring unused_color unused_colors|
      p₀ coloring used_color unused_colors p₀_to_used_color];
      [..| simpl; rewrite Map.find_1 with (1 := p₀_to_used_color)];
      apply IHGraph_s₁_t.
    Defined.

    Definition Proper
      (labeling : Map.t nat)
      (instructions : Instructions.t) :
      Prop :=
      forall
      (owner owner' : Owner.t)
      (color : nat),
      Active owner instructions /\ Map.MapsTo owner color labeling ->
      Active owner' instructions /\ Map.MapsTo owner' color labeling ->
      Owner.eq owner owner'.

    Lemma Graph_Forall :
      forall
      (x : Instructions.t)
      (s t : State.t),
      Instructions.Ok x ->
      Graph.t x s t ->
      State.Ok.t x s ->
      Skip.Forall
        (fun skip : Instructions.t =>
        Sets.count skip <= t.(State.coloring).(Coloring.colors) /\
        Proper t.(State.coloring).(Coloring.labeling) skip)
        x.
    Proof with auto.
      intros x s u Ok_x Graph_s_u Ok_s right Skip_x_right.
      apply Skip.inv in Skip_x_right as (left & H); symmetry in H.
      specialize Graph.split with (1 := Graph_s_u) (2 := H) as
        (t & Graph_s_t & Graph_t_u).
      assert (Ok_right : Instructions.Ok right) by
        (now apply Instructions.Ok.split with left; rewrite H).
      assert (Ok_t : State.Ok.t right t).
        rewrite <- H in *.
        now apply Graph.Ok_morphism with (3 := Graph_s_t).
      split.
        transitivity (t.(State.coloring).(Coloring.colors)).
          rewrite
            <- Nat.add_sub with (Sets.count right) (length t.(State.unused_colors)),
            <- State.Ok.active_plus_unused with right t by assumption.
          apply Nat.le_sub_l.
        enough (Coloring.le t.(State.coloring) u.(State.coloring)) by firstorder.
        now apply Graph.coloring_morphism with (3 := Graph_t_u).
      intros owner owner' color
        Active_MapsTo_owner_color Active_MapsTo_owner'_color.
      now apply Ok_t.(State.Ok.proper) with color;
      rewrite Graph.Active_MapsTo_iff with (2 := Graph_t_u).
    Qed.

    Lemma Graph_Exists :
      forall
      (x : Instructions.t)
      (s t : State.t),
      Instructions.Ok x ->
      Graph.t x s t ->
      State.Ok.t x s ->
      s.(State.coloring).(Coloring.colors) = t.(State.coloring).(Coloring.colors) \/
      Skip.Exists
        (fun skip : Instructions.t =>
        Sets.count skip = t.(State.coloring).(Coloring.colors))
        x.
    Proof with auto.
      intros x s t Ok_x Graph_s_t Ok_s.
      induction Graph_s_t as [
        s|
      u₀ x₀ s₀ s₁ t Transition_s₀_s₁ Graph_s₁_t IHGraph_s₁_t].
        now left.
      assert (Ok_x₀ : Instructions.Ok x₀) by eauto with instructions.
      assert (Ok_s₁ : State.Ok.t x₀ s₁) by
        now apply State.Transition.Ok_morphism with (2 := Transition_s₀_s₁).
      specialize IHGraph_s₁_t as [e₁| H]...
        enough (s₀.(State.coloring).(Coloring.colors) = s₁.(State.coloring).(Coloring.colors) \/ S s₀.(State.coloring).(Coloring.colors) = s₁.(State.coloring).(Coloring.colors) /\ s₁.(State.unused_colors) = []) as [e₀| (e₀ & ?)].
            now left; transitivity s₁.(State.coloring).(Coloring.colors).
          right.
          exists x₀; split; [now constructor 2 with x₀|].
          rewrite <- e₁, <- Nat.add_0_r at 1.
          change 0 with (@length nat []); rewrite <- H.
          symmetry; apply State.Ok.active_plus_unused...
        now destruct Transition_s₀_s₁; [right| left..].
      now right; apply Skip.Exists.cons.
    Qed.

    Lemma graph_spec :
      forall
      x : Instructions.t,
      Instructions.Ok x ->
      Instructions.Closed x ->
      exists
      t : State.t,
      Graph.t x State.initial_state t /\
      Coloring.Ok t.(State.coloring) /\
      Skip.Forall (Proper t.(State.coloring).(Coloring.labeling)) x /\
      Sets.IsChromaticNumber x t.(State.coloring).(Coloring.colors).
    Proof with auto.
      intros x Ok_x Closed_x.
      pose (s := {|
        State.coloring := Coloring.empty;
        State.unused_colors := []
      |}).
      assert (Ok_s : State.Ok.t x s) by
        now apply State.Ok.Empty.Ok.
      specialize Graph.serial with (1 := Ok_x) (2 := Ok_s) as (t & Graph_s_t).
      assert (Ok_t : State.Ok.t [] t) by
        now apply (@Graph.Ok_morphism x [] s t); [rewrite app_nil_r..|].
      exists t.
      split_left.
              assumption.
            apply Ok_t.(State.Ok.coloring).
          1,2 :
            (intros skip Skip_instructions_skip;
            now specialize Graph_Forall with
              (2 := Graph_s_t)
              (4 := Skip_instructions_skip) as (? & ?)).
      specialize Graph_Exists with
        (2 := Graph_s_t)
        (3 := Ok_s) as
        [O_eq_colors| H]; simpl in *...
      now exists x; split; [| rewrite Sets.count_closed].
    Qed.

    Lemma regular_spec :
      forall
      instructions : Instructions.t,
      Instructions.Ok instructions ->
      Instructions.Closed instructions ->
      exists
      coloring : Coloring.t,
      regular instructions = Some coloring /\
      Coloring.Ok coloring /\
      Skip.Forall
        (Proper coloring.(Coloring.labeling))
        instructions /\
        Sets.IsChromaticNumber
          instructions
          coloring.(Coloring.colors).
    Proof with auto.
      intros instructions Ok_instructions Closed_instructions.
      specialize (graph_spec Ok_instructions Closed_instructions) as
        (t & Graph_s_t & Ok_coloring & proper & is_chromatic_number).
      exists t.(State.coloring).
      split_left...
          pose (s := {|
            State.coloring := Coloring.empty;
            State.unused_colors := []
          |}).
          change (regular instructions) with (bind (regular_body instructions s.(State.coloring) s.(State.unused_colors)) (fun x => Some (fst x))).
          change (Graph.t instructions s t) in Graph_s_t.
          now rewrite regular_body_spec with (1 := Graph_s_t).
        apply is_chromatic_number.
      apply is_chromatic_number.
    Qed.
  End Regular.

  Module Pred.
    Definition pred_error
      (n : nat) :
      option nat :=
      match n with
      | O => None
      | S n' => Some n'
      end.

    Notation Pred n m :=
      (pred_error n = Some m).

    Notation Ok n m :=
      (n = S m)
      (only parsing).

    Section Properties.
      Variables
        (m n : nat).

      Lemma None_iff :
        pred_error n = None <->
        n = 0.
      Proof.
        now destruct n as [| n'].
      Qed.

      Lemma eq_None :
        n = 0 ->
        pred_error n = None.
      Proof.
        apply None_iff.
      Qed.

      Lemma None_eq :
        pred_error n = None ->
        n = 0.
      Proof.
        apply None_iff.
      Qed.

      Lemma Some_iff :
        Pred n m <->
        Ok n m.
      Proof.
        now destruct n as [| n'];
          [| split; intros [= ->]].
      Qed.

      Lemma Some_neq :
        Pred n m ->
        Ok n m.
      Proof.
        apply Some_iff.
      Qed.

      Lemma neq_Some :
        n <> 0 ->
        exists m : nat,
          Pred n m /\
          Ok n m.
      Proof.
        now destruct n as [| n'];
          [| exists n'].
      Qed.
    End Properties.

    Lemma pred_error_spec :
      forall n : nat,
        OptionSpec
          (fun m : nat => Ok n m)
          (n = 0)
          (pred_error n).
    Proof.
      intros n.
      now destruct n as [| n'] eqn: Pred;
        constructor.
    Qed.
  End Pred.
  Import Pred(pred_error, pred_error_spec, Pred).

  Module Counter.
    Module State.
      Record t :
        Type :=
        new {
          active : nat;
          colors : nat;
        }.

      Notation initial_state :=
        {|
          State.active := 0;
          State.colors := 0;
        |}.

      Definition from_regular
        (s : Regular.State.t) :
        State.t :=
        {|
          State.active :=
            s.(Regular.State.coloring).(Coloring.colors) -
            length s.(Regular.State.unused_colors);
          State.colors := s.(Regular.State.coloring).(Coloring.colors)
        |}.

      Module Transition.
        Inductive t :
          Instruction.t ->
          relation State.t :=
          | Up_lt :
            forall
            (p₀ : Owner.t)
            (active colors : nat),
            active < colors ->
            t
              (Up p₀)
              {|
                State.active := active;
                State.colors := colors
              |}
              {|
                State.active := S active;
                State.colors := colors
              |}
          | Up_ge :
            forall
            (p₀ : Owner.t)
            (active colors : nat),
            active >= colors ->
            t
              (Up p₀)
              {|
                State.active := active;
                State.colors := colors
              |}
              {|
                State.active := S active;
                State.colors := S active
              |}
          | Down :
            forall
            (p₀ : Owner.t)
            (active colors : nat),
            t
              (Down p₀)
              {|
                State.active := S active;
                State.colors := colors
              |}
              {|
                State.active := active;
                State.colors := colors
              |}.

        Lemma from_regular_morphism :
          forall
          (u₀ : Instruction.t)
          (x₀ : Instructions.t)
          (s₀ s₁ : Regular.State.t),
          Instructions.Ok (u₀ :: x₀) ->
          Regular.State.Ok.t (u₀ :: x₀) s₀ ->
          Regular.State.Transition.t u₀ s₀ s₁ ->
          State.Transition.t u₀ (from_regular s₀) (from_regular s₁).
        Proof with auto with arith.
          assert (S_minus_m_S_n : forall m n : nat, m > n -> S (m - S n) = m - n).
            intros m n m_gt_n.
            now rewrite <- Nat.sub_succ_l, Nat.sub_succ.
          intros u₀ x₀ s₀ s₁ Ok_x Ok_s₀ Transition_s₀_s₁.
          specialize (Regular.State.Ok.active_plus_unused Ok_x Ok_s₀) as H.
          induction Transition_s₀_s₁ as [
              p₀ coloring|
            p₀ coloring unused_color unused_colors|
          p₀ coloring used_color unused_colors p₀_to_used_color];
          unfold from_regular; simpl.
              rewrite Nat.sub_0_r; constructor...
            assert (unused_le_colors : S (length unused_colors) <= coloring.(Coloring.colors)).
              apply Nat.le_le_add_le with
                0 (Regular.State.Ok.Sets.count (Up p₀ :: x₀))...
              rewrite Nat.add_0_r, Nat.add_comm; apply Nat.eq_le_incl...
            rewrite <- S_minus_m_S_n with (n := length unused_colors);
              [constructor|]...
          assert (unused_lt_colors : length unused_colors < coloring.(Coloring.colors)).
              apply Nat.lt_le_add_lt with
                0 (Regular.State.Ok.Sets.count (Notations.Down p₀ :: x₀)).
              rewrite Regular.State.Ok.Sets.count_Down...
            rewrite Nat.add_0_r, Nat.add_comm; apply Nat.eq_le_incl...
          now rewrite <- S_minus_m_S_n with (n := length unused_colors);
            [constructor|].
        Qed.
      End Transition.

      Module Graph.
        Inductive t :
          Instructions.t ->
          relation State.t :=
          | Nil :
            forall
            s : State.t,
            t [] s s
          | Cons :
            forall
            (u₀ : Instruction.t)
            (x₀ : Instructions.t)
            (s₀ s₁ u : State.t),
            Transition.t u₀ s₀ s₁ ->
            t x₀ s₁ u ->
            t (u₀ :: x₀) s₀ u.

        Lemma from_regular_morphism :
          forall
          (x : Instructions.t)
          (s t : Regular.State.t),
          Instructions.Ok x ->
          Regular.State.Ok.t x s ->
          Regular.State.Graph.t x s t ->
          State.Graph.t x (from_regular s) (from_regular t).
        Proof with eauto with instructions.
          intros x s t Ok_x Ok_s Graph_s_t.
          induction Graph_s_t as [
            s|
          u₀ x₀ s₀ s₁ t Transition_s₀_s₁ Graph_s₁_t IHGraph_s₁_t].
            constructor.
          constructor 2 with (from_regular s₁).
            now apply Transition.from_regular_morphism with x₀.
          apply IHGraph_s₁_t...
          now apply Regular.State.Transition.Ok_morphism with (3 := Ok_s).
        Qed.

        Lemma spec :
          forall
          instructions : Instructions.t,
          Instructions.Ok instructions ->
          Instructions.Closed instructions ->
          exists
          t : State.t,
          State.Graph.t instructions State.initial_state t /\
          Regular.State.Ok.Sets.IsChromaticNumber instructions t.(State.colors).
        Proof with auto with arith.
          intros x Ok_x Closed_x.
          pose (s := Regular.State.initial_state).
          assert (Ok_s : Regular.State.Ok.t x s) by
            now apply Regular.State.Ok.Empty.Ok.
          specialize (Regular.graph_spec Ok_x Closed_x) as
            (t & Graph_s_t & Ok_coloring & _ & is_chromatic_number).
          exists (State.from_regular t).
          split.
            change (State.Graph.t x (State.from_regular s) (State.from_regular t)).
            now apply State.Graph.from_regular_morphism.
          apply is_chromatic_number.
        Qed.
      End Graph.
    End State.

    Fixpoint counter_body
      (x : Instructions.t)
      (active : nat)
      (colors : nat) :
      option nat :=
      match x with
      | [] =>
        Some colors
      | Up p₀ :: x₀ =>
        counter_body
          x₀
          (S active)
          (max (S active) colors)
      | Down p₀ :: x₀ =>
        bind (pred_error active) (fun active' : nat =>
          counter_body
            x₀
            active'
            colors)
      end.

    Definition counter
      (x : Instructions.t) :
      option nat :=
      counter_body x O O.

    Lemma counter_body_spec :
      forall
      (x : Instructions.t)
      (s t : State.t),
      State.Graph.t x s t ->
      counter_body x s.(State.active) s.(State.colors) =
      Some t.(State.colors).
    Proof.
      intros x s t Graph_s_t.
      induction Graph_s_t as [
        s|
      u₀ x₀ s₀ s₁ t Transition_s₀_s₁ Graph_s₁_t IHGraph_s₁_t].
        reflexivity.
      induction Transition_s₀_s₁ as [
          p₀ active colors active_lt_colors|
        p₀ active colors active_ge_colors|
      p₀ active colors]; [
        change (counter_body x₀ (S active) (max (S active) colors) = Some t.(State.colors))..|
      assumption].
        now rewrite max_r.
      now rewrite max_l; [| apply le_S].
    Defined.

    Lemma counter_spec :
      forall
      instructions : Instructions.t,
      Instructions.Ok instructions ->
      Instructions.Closed instructions ->
      exists
      colors : nat,
      counter instructions = Some colors /\
      Regular.State.Ok.Sets.IsChromaticNumber instructions colors.
    Proof with auto with arith.
      intros x Ok_x Closed_x.
      specialize (State.Graph.spec Ok_x Closed_x) as
        (t & Graph_s_t & is_chromatic_number_x_t).
      exists t.(State.colors).
      split; [| assumption].
      apply counter_body_spec with (1 := Graph_s_t).
    Qed.
  End Counter.

  Module Fixed.
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

    Module Min (Import O : Ord).
      Module Import Facts := OrdFacts O.
      Module Import OTF := Ord_to_OTF O.

      Definition Min
        (x : list t)
        (n : nat)
        (v : t) :
        Prop :=
        ForNth (fun (m : nat) (w : t) =>
          ((m < n)%nat -> v < w) /\
          ((m > n)%nat -> v <= w)) x /\
        Nth x n v.

      Lemma Min_fun : forall x m v n w,
        Min x m v ->
        Min x n w ->
        m = n /\ v = w.
      Proof.
        intros x m v n w (Min_m_v & m_to_v) (Min_n_w & n_to_w).
        unfold ForNth in *.
        specialize Min_m_v with (1 := n_to_w).
        specialize Min_n_w with (1 := m_to_v).
        destruct (lt_eq_lt_dec m n) as
          [[m_lt_n| ->]| m_gt_n].
            enough (w < w) by order.
            enough (w < v /\ v <= w) as (w_lt_v & v_le_w) by order.
            now split; [apply Min_n_w| apply Min_m_v].
          enough (Some v = Some w) as [= v_eq_w] by easy.
          now transitivity (nth_error x n).
        enough (v < v) by order.
        enough (v < w /\ w <= v) as (v_lt_w & w_le_v) by order.
        now split; [apply Min_m_v| apply Min_n_w].
      Qed.

      Section Properties.
        Variables
          (u₀ : t)
          (x₀ : list t)
          (n : nat)
          (v : t).

        Lemma nil_inv :
          ~ Min [] n v.
        Proof.
          intros (_ & n_to_v).
          now apply Nth.nil_inv in n_to_v.
        Qed.

        Lemma nil_iff :
          Min [] n v <-> False.
        Proof.
          split;
            [apply nil_inv| easy].
        Qed.

        Lemma cons_le :
          ForNth (fun n u => u₀ <= u) x₀ ->
          Min (u₀ :: x₀) O u₀.
        Proof.
          intros u₀_le_x₀.
          split; [| easy].
          intros m w m_to_w.
          split.
            intros m_lt_O; contradict m_lt_O; apply Nat.nlt_0_r.
          destruct m as [| m']; intros m_gt_O.
            contradict m_gt_O; apply Nat.nlt_0_r.
          now apply u₀_le_x₀ with m'.
        Qed.

        Lemma cons_gt :
          u₀ > v ->
          Min x₀ n v ->
          Min (u₀ :: x₀) (S n) v.
        Proof.
          intros not_u₀_le_x₀ Min_n_v.
          split; [| apply Min_n_v].
          apply ForNth.cons; [split; order|].
          intros m w m_to_w.
          now unfold gt; rewrite <- 2!Nat.succ_lt_mono;
            apply Min_n_v.
        Qed.
      End Properties.

      Fixpoint minimum_body
        (x : list t)
        (index : nat)
        (n : nat)
        (v : t) :
        nat * t :=
        match x with
        | [] => (n, v)
        | u₀ :: x₀ =>
          if u₀ <? v then
            minimum_body x₀ (S index) index u₀
          else
            minimum_body x₀ (S index) n v
        end.

      Definition minimum
        (x : list t) :
        option (nat * t) :=
        match x with
        | [] => None
        | u₀ :: x₀ => Some (minimum_body x₀ 1 O u₀)
        end.

      Notation Minimum
        x
        n
        v :=
        (minimum x = Some (n, v)).

      Lemma minimum_body_spec : forall
        (x : list t)
        (index : nat)
        (n : nat)
        (v : t),
        let (n', v') := minimum_body x index n v in
        (v' <= v) /\
        ((n' = n /\
        v' = v /\
        ForNth (fun (m : nat) (w : t) => v' <= w) x) \/
        (v' < v /\
          exists m : nat,
            n' = index + m /\
            Min x m v')).
      Proof.
        induction x as [| u₀ x₀ IHx₀]; intros index n v.
          split; [| left].
            reflexivity.
            split; [easy|].
            split; [easy|].
            apply ForNth.nil.
        simpl; destruct (ltb_spec u₀ v) as [u₀_lt_v| u₀_ge_v].
          specialize (IHx₀ (S index) index u₀).
          destruct (minimum_body x₀ (S index) index u₀) as [n' v'],
            IHx₀ as [v'_le_u₀ IHx₀].
          split; [transitivity u₀; order|].
          destruct IHx₀ as [(-> & -> & u₀_le_x₀)| (v'_lt_u₀ & m' & IHx₀)]; right.
            split; [easy|].
            now exists O; split; [rewrite Nat.add_0_r| apply cons_le].
          split; [now transitivity u₀|].
          now exists (S m'); split;
            [rewrite Nat.add_succ_r| apply cons_gt, IHx₀].
        specialize (IHx₀ (S index) n v).
        destruct (minimum_body x₀ (S index) n v) as [n' v'],
          IHx₀ as [v'_le_u₀ IHx₀].
        split; [easy|].
        destruct IHx₀
          as [(n'_eq_n & v'_eq_v & v'_le_x₀)| (v'_lt_v & m' & IHx₀)];
          [left| right].
          repeat split; try easy.
          now apply ForNth.cons; [order|].
        split; [order|].
        now exists (S m'); split;
          [rewrite Nat.add_succ_r| apply cons_gt; [order|]].
      Qed.

      Lemma minimum_spec : forall x : list t,
        OptionSpec (fun min : nat * t => let (n, v) := min in Min x n v) (x = []) (minimum x).
      Proof.
        destruct x as [| u₀ x₀]; constructor.
          reflexivity.
        specialize minimum_body_spec with x₀ 1 O u₀ as IHx₀.
        destruct (minimum_body x₀ 1 O u₀) as (n' & v').
        now destruct IHx₀ as
          [_ [(-> & -> & IHx₀)| (v'_lt_u₀ & m' & -> & IHx₀)]];
          [apply cons_le| apply cons_gt].
      Qed.

      Section Properties.
        Variables
          (x : list t)
          (n : nat)
          (v : t).

        Lemma None_iff :
          minimum x = None <->
          x = [].
        Proof.
          clear n v.
          destruct (minimum_spec x) as [(n, v) (_ & n_to_v)| x_eq_nil];
            [destruct x as [| u₀ x₀]|]; try easy.
          now apply Nth.nil_inv in n_to_v.
        Qed.

        Lemma None_eq :
          minimum x = None ->
          x = [].
        Proof.
          apply None_iff.
        Qed.

        Lemma eq_None :
          x = [] ->
          minimum x = None.
        Proof.
          apply None_iff.
        Qed.

        Lemma Some_iff :
          Minimum x n v <->
          Min x n v.
        Proof.
          destruct (minimum_spec x) as [(n', v') Min_n'_v'| ->].
            split.
              now intros [= -> ->].
            intros Min_n_v.
            enough (n = n' /\ v = v') as (-> & ->) by easy.
            now apply Min_fun with x.
          unfold Min.
          now rewrite Nth.nil_iff.
        Qed.

        Lemma neq_Some :
          x <> [] ->
          exists
            (c : nat)
            (v : t),
            Minimum x c v /\
            Min x c v.
        Proof.
          clear n v.
          now destruct (minimum_spec x) as [(n & v) Min_n_v| ?];
            intros x_neq_nil;
            [exists n, v|].
        Qed.

        Lemma Some_neq :
          Minimum x n v ->
          Min x n v.
        Proof.
          apply Some_iff.
        Qed.
      End Properties.
    End Min.
    Module Min' := Min Nat.

    Notation add_S
      self
      p₀
      c₀ :=
      (Coloring.new
        (max (S c₀) self.(Coloring.colors))
        (Map.add p₀ c₀%nat self.(Coloring.labeling))).

    Fixpoint fixed_body
      (instructions : list Instruction.t)
      (coloring : Coloring.t)
      (counts : list nat) :
      option Coloring.t :=
      match instructions with
      | Up p₀ :: x₀ =>
        bind (Min'.minimum counts) (fun min => let (color, count) := min in
        bind (replace counts color (S count)) (fun counts' =>
          let coloring := add_S coloring p₀ color in
          fixed_body x₀ coloring counts'
          ))
      | Down p₀ :: x₀ =>
          bind (Coloring.find coloring p₀) (fun color =>
          bind (nth_error counts color) (fun count =>
          bind (pred_error count) (fun count' =>
          bind (replace counts color count') (fun counts' =>
            fixed_body x₀ coloring counts'))))
      | [] => ret coloring
      end.

    Definition fixed
      (instructions : Instructions.t)
      (colors : nat) :
      option Coloring.t :=
      fixed_body instructions Coloring.empty (repeat O colors).

    Lemma StronglyExtensional
      (coloring : Coloring.t) :
      forall p p' c c',
        Coloring.MapsTo coloring p c ->
        Coloring.MapsTo coloring p' c' ->
        c <> c' ->
        ~ Owner.eq p p'.
    Proof.
      intros p p' c c' p_to_c p'_to_c' c_neq_c'.
      contradict c_neq_c'; rewrite c_neq_c' in p_to_c.
      now apply MapsTo_fun with (1 := p_to_c).
    Qed.

    Module M := MSetWeakList.Make Owner.
    Module M_Facts := MSetFacts.Facts M.
    Module M_Properties := MSetProperties.WProperties M.

    Lemma add_eq_iff : forall
      (s : M.t)
      (x y : Owner.t),
      Owner.eq x y ->
        M.In y (M.add x s) <->
        True.
    Proof.
      intros.
      rewrite M_Facts.add_iff; tauto.
    Qed.

    Definition Synced
      (instructions : list Instruction.t)
      (coloring : Coloring.t) :
      Prop := forall
        owner : Owner.t,
        (Active owner instructions ->
        Coloring.Contains coloring owner) /\
        (Ahead owner instructions ->
          ~ Coloring.Contains coloring owner).

    Module State.
      Record t : Type := new {
        instructions : Instructions.t;
        coloring : Coloring.t;
        counts : list nat
      }.

      Inductive Fixed : relation State.t :=
      | Fixed_Up :
        forall
          (p₀ : Owner.t)
          (x₀ : Instructions.t)
          (coloring : Coloring.t)
          (counts counts' : list nat)
          (c₀ v₀ : nat),
          Min'.Min counts c₀ v₀ ->
          Replace.Ok counts c₀ (S v₀) counts' ->
          Fixed (new x₀ (add_S coloring p₀ c₀) counts') (new (Up p₀ :: x₀) coloring counts)
      | Fixed_Down :
        forall
          (p₀ : Owner.t)
          (x₀ : Instructions.t)
          (coloring : Coloring.t)
          (counts counts' : list nat)
          (c₀ v₀' : nat),
          Coloring.MapsTo coloring p₀ c₀ ->
          Nth counts c₀ (S v₀') ->
          Replace.Ok counts c₀ v₀' counts' ->
          Fixed (new x₀ coloring counts') (new (Down p₀ :: x₀) coloring counts).

      Module Ok.
        Section Ok.
          Variable
            (s : State.t).

          Definition Counts :
            Prop :=
            ForNth
              (fun (color count : nat) =>
              exists owners : M.t,
                (forall owner : Owner.t,
                M.In owner owners <->
                  Active owner s.(instructions) /\
                  Coloring.MapsTo s.(coloring) owner color) /\
                M.cardinal owners = count)
              s.(counts).

          Definition Length :
            Prop :=
            s.(coloring).(Coloring.colors) <= length s.(counts).

          Record t : Prop := new {
            instructions : Instructions.Ok s.(State.instructions);
            coloring : Coloring.Ok s.(State.coloring);
            synced : Synced s.(State.instructions) s.(State.coloring);
            counts : Counts;
            length : Length;
          }.

          Corollary counts_O :
            t ->
            forall
              color : nat,
              s.(State.coloring).(Coloring.colors) <= color < List.length s.(State.counts) ->
              Nth s.(State.counts) color 0.
          Proof.
            intros Ok_s c (colors_le_c & c_lt_counts).
            specialize NthError.lt_Some with (1 := c_lt_counts) as (v & c_to_v).
            enough (v = 0) as -> by easy.
            apply Ok_s.(counts) in c_to_v as (owners & Ok_owners & <-).
            enough (M.Empty owners) by
              now apply M_Properties.cardinal_Empty.
            intros p.
            enough (~ Coloring.MapsTo s.(State.coloring) p c) by
                now rewrite Ok_owners.
            enough (c_nlt_colors : ~ c < s.(State.coloring).(Coloring.colors)) by
              now contradict c_nlt_colors; apply Ok_s.(coloring); exists p.
            auto with arith.
          Qed.

          Corollary Min_le_colors :
            t ->
            forall
              c v : nat,
              Min'.Min s.(State.counts) c v ->
              c <= s.(State.coloring).(Coloring.colors).
          Proof with auto with arith.
            intros Ok_s c v (Min_c_v & c_to_v).
            enough (~ c > s.(State.coloring).(Coloring.colors)) by
              now apply not_gt.
            specialize Nat.nlt_0_r with v as c_gt_colors;
              contradict c_gt_colors.
            apply Min_c_v with (2 := c_gt_colors), counts_O...
            enough (s.(State.coloring).(Coloring.colors) < List.length s.(State.counts))...
            transitivity c;
              [| apply NthError.Some_lt with v]...
          Qed.
        End Ok.
      End Ok.

      Section Facts.
        Variables
          (s₀ s₁ : State.t)
          (Fixed_s₁_s₀ : Fixed s₁ s₀)
          (Ok_s₀ : Ok.t s₀).

        Let Ok_instructions₀ :
          Instructions.Ok s₀.(instructions) :=
          Ok_s₀.(Ok.instructions).
        Let Ok_coloring₀ :
          Coloring.Ok s₀.(coloring) :=
          Ok_s₀.(Ok.coloring).
        Let Synced_s₀ :
          Synced s₀.(instructions) s₀.(coloring) :=
          Ok_s₀.(Ok.synced).
        Let Ok_counts₀ :
          Ok.Counts s₀ :=
          Ok_s₀.(Ok.counts).
        Let Ok_length₀ :
          Ok.Length s₀ :=
          Ok_s₀.(Ok.length).

        Ltac destruct_Fixed :=
          destruct Fixed_s₁_s₀ as
          [p₀ x₀ coloring₀ counts₀ counts₁ c₀ v₀ (Min_c₀_v₀ & c₀_to_v₀) Replace_counts₁|
          p₀ x₀ coloring₀ counts₀ counts₁ c₀ v₀' p₀_to_c₀ c₀_to_v₀ Replace_counts₁];
          [apply Instructions.Ok.cons_Up_iff in Ok_instructions₀ as (Active_p₀_x₀ & Ok_x₀)| apply Instructions.Ok.cons_Down_iff in Ok_instructions₀ as (Absent_p₀_x₀ & Ok_x₀)].

        Let Pred_s₁_s₀ :
          Tail s₀.(instructions) s₁.(instructions).
        Proof.
          destruct_Fixed; constructor.
        Qed.

        Let Ok_instructions₁ :
          Instructions.Ok s₁.(instructions).
        Proof.
          pose proof (Ok_s₀.(Ok.instructions)).
          now rewrite <- Pred_s₁_s₀.
        Qed.

        Let Ok_coloring₁ :
          Coloring.Ok s₁.(coloring).
        Proof with instructions_tac.
          destruct_Fixed; cbn - [max] in *...
          assert (not_In_p₀ : ~ Coloring.Contains coloring₀ p₀).
            apply Synced_s₀...
          enough (c₀ < coloring₀.(Coloring.colors) \/ c₀ = coloring₀.(Coloring.colors)) as [c₀_lt_colors₀| ->].
              rewrite max_r; [apply Coloring.Ok.add_lt|]...
            rewrite max_l; [apply Coloring.Ok.add_eq|]...
          enough (c₀ <= coloring₀.(Coloring.colors)) by now apply le_lt_or_eq.
          now apply Ok.Min_le_colors with
            (s :=new (Up p₀ :: x₀) coloring₀ counts₀)
            (c := c₀)
            (v := v₀).
        Qed.

        Let Synced_s₁ :
          Synced s₁.(instructions) s₁.(coloring).
        Proof with (simpl; instructions_tac).
          destruct_Fixed;
            intros p; split; simpl.
                intros Active_p_x₀; apply add_in_iff.
                destruct (Owner.eq_dec p₀ p) as [p₀_eq_p| p₀_neq_p];
                  [left| right; apply Synced_s₀]...
              intros Ahead_p₀_x₀.
              apply add_not_in_iff; split.
                contradict Ahead_p₀_x₀; rewrite <- Ahead_p₀_x₀...
              apply Synced_s₀...
            intros Active_p_x₀; apply Synced_s₀...
          intros Ahead_p_x₀; apply Synced_s₀...
        Qed.

        Let length_eq :
          length s₁.(counts) = length s₀.(counts).
        Proof.
          symmetry; destruct_Fixed; apply Replace_counts₁.
        Qed.

        Let Ok_length₁ :
          Ok.Length s₁.
        Proof with auto.
          unfold Ok.Length; rewrite length_eq.
          destruct_Fixed...
          apply Nat.max_lub...
          simpl; apply NthError.Some_lt with v₀...
        Qed.

        Let Ok_counts₁ :
          Ok.Counts s₁.
        Proof with (simpl; instructions_tac).
          unfold Ok.Counts, ForNth in Ok_counts₀.
          destruct_Fixed.
            intros c v c_to_v.
            destruct Replace_counts₁ as
              (c₀_lt_counts₀ & _ & c₀_to_S_v₀ & H).
            destruct (Nat.eq_dec c c₀) as [->| c_neq_c₀].
              specialize Ok_counts₀ with (1 := c₀_to_v₀) as
                (owners & owners_iff & owners_length).
              exists (M.add p₀ owners); simpl in *; split.
                intro p; destruct (Owner.eq_dec p₀ p) as
                  [p₀_eq_p| p₀_neq_p].
                  symmetry in p₀_eq_p.
                  now rewrite
                    add_eq_iff,
                    add_eq_mapsto_iff,
                    p₀_eq_p.
                now rewrite
                  M_Facts.add_neq_iff,
                  owners_iff,
                  add_neq_mapsto_iff,
                  Active.cons_Up_iff.
              rewrite M_Properties.add_cardinal_2, owners_length.
                now enough (Some (S v₀) = Some v) as [=];
                  [| transitivity (nth_error counts₁ c₀)].
              enough (~ Active p₀ (Up p₀ :: x₀)) by
                (rewrite owners_iff; tauto).
              enough (Owner.eq p₀ p₀) by
                (rewrite Active.cons_Up_iff; tauto).
              reflexivity.
            specialize Ok_counts₀ with c v as
              (owners & owners_iff & owners_length);
              [now rewrite H|].
            exists owners; split; [| assumption].
            intros p; simpl in *.
            rewrite owners_iff.
            split; intros (Active_p & p_to_c).
              enough (p₀_neq_p : ~ Owner.eq p₀ p).
                apply Active.cons_Up_iff in Active_p.
                now rewrite add_neq_mapsto_iff.
              contradict Active_p; rewrite Active_p...
            apply add_mapsto_iff in p_to_c as
              [(_ & c₀_eq_c)| (p₀_neq_p & p_to_c₀)];
              [now contradict c_neq_c₀|].
            split...
          simpl in *.
          intros c v' c_to_v'.
          assert (c_lt_counts₀ : c < length counts₀).
            rewrite <- length_eq.
            now apply NthError.Some_lt with v'.
          specialize NthError.lt_Some with (1 := c_lt_counts₀) as
            (v & c_to_v).
          destruct Replace_counts₁ as
            (c₀_lt_counts₀ & _ & c₀_to_v₀' & H).
          specialize Ok_counts₀ with (1 := c_to_v) as
            (owners & owners_iff & owners_length).
          destruct (Nat.eq_dec c c₀) as [->| c_neq_c₀].
            2: {
              exists owners.
              assert (Some v = Some v') as [= <-] by
                now rewrite <- c_to_v, <- c_to_v'; apply H.
              split; [| assumption].
              intros p.
              rewrite owners_iff, Active.cons_Down_iff...
              enough (Coloring.MapsTo coloring₀ p c -> ~ Owner.eq p₀ p) by tauto.
              intros p_to_c.
              now apply StronglyExtensional with coloring₀ c₀ c;
                [..| change (complement Logic.eq c₀ c)].
            }
          exists (M.remove p₀ owners); split.
            intros p.
            rewrite
              M.remove_spec,
              owners_iff,
              Active.cons_Down_iff...
            enough ((Owner.eq p₀ p \/ Active p x₀) /\
            ~ Owner.eq p p₀ <-> Active p x₀) by firstorder.
            assert (Owner.eq p₀ p <-> Owner.eq p p₀) as -> by easy.
            enough (Active p x₀ -> ~ Owner.eq p p₀); [tauto|].
            intros Active_p_x₀; contradict Active_p_x₀; rewrite Active_p_x₀...
          change (pred (S (M.cardinal (M.remove p₀ owners))) = v').
          rewrite M_Properties.remove_cardinal_1, owners_length; [| apply owners_iff]...
          enough (Some v = Some (S v₀') /\ Some v' = Some v₀') as
            ([= ->] & [= ->]) by reflexivity.
          now rewrite <- c_to_v, <- c₀_to_v₀, <- c_to_v', <- c₀_to_v₀'.
        Qed.

        Lemma Ok_s₁ :
          Ok.t s₁.
        Proof.
          now constructor.
        Qed.
      End Facts.
    End State.

    Definition Graph :=
      clos_refl_trans_n1 _ State.Fixed.

    Inductive Graph_Contains (s' : State.t) :
      forall s : State.t,
      Graph s' s ->
      State.t ->
      Prop :=
    | Contains_rtn1_refl :
      Graph_Contains (rtn1_refl State.t State.Fixed s') s'
    | Contains_rtn1_trans_left :
      forall
        (s₀ s₁ : State.t)
        (Fixed_s₁_s₀ : State.Fixed s₁ s₀)
        (Graph_s'_s₁ : Graph s' s₁),
        Graph_Contains (rtn1_trans _ _ _ _ _ Fixed_s₁_s₀ Graph_s'_s₁) s₀
    | Contains_rtn1_trans_right :
      forall
        (s₀ s₁ r : State.t)
        (Fixed_s₁_s₀ : State.Fixed s₁ s₀)
        (Graph_s'_s₁ : Graph s' s₁),
        Graph_Contains Graph_s'_s₁ r ->
        Graph_Contains (rtn1_trans _ _ _ _ _ Fixed_s₁_s₀ Graph_s'_s₁) r.

    Instance Fixed_Graph_subrelation :
      subrelation State.Fixed Graph.
    Proof.
      intros s' s Fixed_s'_s.
      now apply clos_rtn1_step.
    Qed.

    Generalizable Variables A R f.

    Instance Graph_morphism
      `{PreOrder_R : @PreOrder A R}
      `{Proper_f : Proper _ (State.Fixed --> R) f} :
      Proper (Graph --> R) f.
    Proof.
      intros s s'; induction 1 as [| s₀ s₁ Fixed_s₁_s₀]; [reflexivity|].
      now transitivity (f s₀);
        [rewrite Fixed_s₁_s₀|].
    Qed.

    Add Parametric Relation : Prop impl
      reflexivity proved by impl_Reflexive
      transitivity proved by impl_Transitive
      as PreOrder_impl.

    Add Parametric Morphism : State.Ok.t with signature
      State.Fixed --> impl as Ok_morphism.
    Proof.
      intros s₀ s₁ Fixed_s₁_s₀ Ok_s₀.
      now apply State.Ok_s₁ with s₀.
    Qed.

    Add Parametric Morphism : (compose (length (A := nat)) State.counts) with signature
      State.Fixed ++> eq as length_morphism.
    Proof.
      intros s₁ s₀ Fixed_s₁_s₀.
      symmetry; destruct Fixed_s₁_s₀ as
        [p₀ x₀ coloring₀ counts₀ counts₁ c₀ v₀ (Min_c₀_v₀ & c₀_to_v₀) Replace_counts₁|
        p₀ x₀ coloring₀ counts₀ counts₁ c₀ v₀' p₀_to_c₀ c₀_to_v₀ Replace_counts₁];
        apply Replace_counts₁.
    Qed.

    Add Parametric Morphism : State.instructions with signature
      State.Fixed --> Tail (A := Instruction.t) as instructions_morphism.
    Proof.
      intros v₀ v₁ Counter_v₁_v₀.
      induction Counter_v₁_v₀; constructor.
    Qed.

    Lemma coloring_morphism :
      forall
        s₀ s₁ : State.t,
        State.Ok.t s₀ ->
        State.Fixed s₁ s₀ ->
        Coloring.le s₀.(State.coloring) s₁.(State.coloring).
    Proof with instructions_tac.
      intros s₀ s₁ Ok_s₀ Fixed_s₁_s₀.
      destruct Fixed_s₁_s₀ as
        [p₀ x₀ coloring₀ counts₀ counts₁ c₀ v₀ (Min_c₀_v₀ & c₀_to_v₀) Replace_counts₁|
        p₀ x₀ coloring₀ counts₀ counts₁ c₀ v₀' p₀_to_c₀ c₀_to_v₀ Replace_counts₁].
        split.
          cbn - [max]; auto with arith.
        cbn; intros p c p_to_c.
        apply Map.add_2 with (2 := p_to_c).
        contradict p_to_c; rewrite <- p_to_c.
        enough (H : ~ Coloring.Contains coloring₀ p₀) by
          now contradict H; exists c.
        enough (Ahead p₀ (Up p₀ :: x₀)) by
          now apply Ok_s₀.(State.Ok.synced)...
      now split.
    Qed.

    Lemma Graph_coloring_morphism :
      forall
        s' s : State.t,
        State.Ok.t s ->
        Graph s' s ->
        Coloring.le s.(State.coloring) s'.(State.coloring).
    Proof with instructions_tac.
      intros s' s Ok_s Graph_s'_s.
      induction Graph_s'_s as [| s₁ s₀ Fixed_s₁_s₀ Graph_s'_s₁ IHs₁].
        reflexivity.
      now transitivity s₁.(State.coloring);
        [apply coloring_morphism| apply IHs₁; rewrite Fixed_s₁_s₀].
    Qed.

    Lemma fixed_body_spec :
      forall
        (instructions : Instructions.t)
        (coloring : Coloring.t)
        (counts : list nat)
        (s := State.new instructions coloring counts),
        State.Ok.t s ->
        length s.(State.counts) <> 0 ->
        exists s' : State.t,
          Graph s' s /\
          fixed_body instructions coloring counts = Some s'.(State.coloring).
    Proof with (simpl; instructions_tac).
      induction instructions as [| [[|] p₀] x₀ IHx₀];
        intros coloring₀ counts₀ s₀ Ok_s₀ counts₀_neq_nil.
          exists s₀; repeat constructor.
        simpl; destruct (Min'.minimum_spec counts₀) as
          [(c₀ & v₀) Min_c₀_v₀| counts_eq_nil];
          [| now apply length_zero_iff_nil in counts_eq_nil];
          simpl.
        specialize Replace.lt_Some with _ counts₀ c₀ (S v₀) as
          (counts₁ & -> & Replace_counts₁).
          apply NthError.Some_lt with v₀, Min_c₀_v₀.
        pose (s₁ := State.new x₀ (add_S coloring₀ p₀ c₀) counts₁).
        assert (Fixed_s₁_s₀ : State.Fixed s₁ s₀) by
          now constructor 1 with v₀.
        assert (Ok_s₁ : State.Ok.t s₁) by
          now rewrite Fixed_s₁_s₀.
        specialize IHx₀ with (1 := Ok_s₁) as
          (s' & Graph_s'_s₁ & H).
          change (compose (@length nat) State.counts s₁ <> 0).
          now rewrite Fixed_s₁_s₀.
        now exists s'; split;
          [constructor 2 with s₁|].
      assert (Active_p₀_s₀ : Active p₀ s₀.(State.instructions)) by
        (apply Active.cons_Down_hd;
        exact (Ok_s₀.(State.Ok.instructions))).
      simpl; specialize find_In_Some as (c₀ & -> & p₀_to_c₀).
        now apply Ok_s₀.(State.Ok.synced).
      specialize NthError.lt_Some with _ counts₀ c₀ as
        (v₀ & c₀_to_v₀).
        apply lt_le_trans with s₀.(State.coloring).(Coloring.colors).
          now apply Ok_s₀.(State.Ok.coloring); exists p₀.
        apply Ok_s₀.(State.Ok.length).
      simpl; rewrite c₀_to_v₀; simpl.
      specialize Pred.neq_Some with v₀ as
        (v₀' & -> & Ok_v₀_v₀').
        specialize Ok_s₀.(State.Ok.counts) as
          (owners₀ & owners₀_iff & owners₀_length).
          exact c₀_to_v₀.
        rewrite <- owners₀_length, <- M_Properties.cardinal_Empty.
        now enough (In_p₀_owners₀ : M.In p₀ owners₀);
          [contradict In_p₀_owners₀| apply owners₀_iff].
      simpl; specialize Replace.lt_Some with _ counts₀ c₀ v₀' as
        (counts₁ & -> & Replace_counts₁).
        now apply NthError.Some_lt with v₀.
      pose (s₁ := State.new x₀ coloring₀ counts₁).
      assert (Fixed_s₁_s₀ : State.Fixed s₁ s₀) by
        now rewrite Ok_v₀_v₀' in c₀_to_v₀; constructor 2 with c₀ v₀'.
      assert (Ok_s₁ : State.Ok.t s₁).
        now rewrite Fixed_s₁_s₀.
      specialize IHx₀ with (1 := Ok_s₁) as
        (s' & Graph_s'_s₁ & H).
        change (compose (@length nat) State.counts s₁ <> 0).
        now rewrite Fixed_s₁_s₀.
      now exists s'; split;
        [constructor 2 with s₁|].
    Qed.

    Lemma Ahead_impl_Contains :
    forall
      s' s : State.t,
      s'.(State.instructions) = [] ->
      Graph s' s ->
      State.Ok.t s ->
      forall p : Owner.t,
        Ahead p s.(State.instructions) ->
        Coloring.Contains s'.(State.coloring) p.
    Proof with (simpl; instructions_tac).
      intros s' s instructions'_eq_nil.
      induction 1 as [| s₁ s₀ Fixed_s₁_s₀ Graph_s'_s₁ IHs₁];
        intros Ok_s₀ p Ahead_p;
        [| assert(Ok_s₁ : State.Ok.t s₁) by now rewrite Fixed_s₁_s₀].
        contradict Ahead_p; rewrite instructions'_eq_nil...
      specialize Tail.inv with _ s₁.(State.instructions) s₀.(State.instructions)
        as [([|] & p₀) H];
        [now apply instructions_morphism| rewrite H in Ahead_p..].
        apply Instructions.Ahead.cons_Up_iff in Ahead_p as [<-| Ahead_p].
          enough (Coloring.Contains s₁.(State.coloring) p₀) as (c & p_to_c) by
            now exists c; apply Graph_coloring_morphism with (2 := Graph_s'_s₁).
          apply Ok_s₁.(State.Ok.synced), Instructions.Ok.cons_Up_iff.
          replace (Up p₀ :: s₁.(State.instructions)) with
            (s₀.(State.instructions)).
          now apply State.Ok.instructions.
        now apply IHs₁.
      apply Instructions.Ahead.cons_Down_iff in Ahead_p.
      now apply IHs₁.
    Qed.

    Module Assumptions.
      Import MSets.

      Module M := MSetWeakList.Make Owner.
      Module Import M_Facts := MSetFacts.Facts M.
      Module Import M_Properties := MSetProperties.WProperties M.

      Lemma add_eq_iff : forall
        (s : M.t)
        (x y : Owner.t),
        Owner.eq x y ->
          M.In y (M.add x s) <->
          True.
      Proof.
        intros.
        rewrite add_iff; tauto.
      Qed.

      Module Count.
        Definition Ok
          (instructions : Instructions.t)
          (coloring : Coloring.t)
          (color : nat)
          (count : nat) :
          Prop :=
          exists owners : M.t,
            (forall owner : Owner.t,
              M.In owner owners <->
                Active owner instructions /\
                Coloring.MapsTo coloring owner color) /\
            M.cardinal owners = count.
      End Count.

      Definition Ok
        (instructions : Instructions.t)
        (coloring : Coloring.t)
        (counts : list nat) :
        Prop :=
        Instructions.Ok instructions /\
        Coloring.Ok coloring /\
        (coloring.(Coloring.colors) <= length counts /\ length counts <> O) /\
        Synced instructions coloring /\
        ForNth (Count.Ok instructions coloring) counts /\
        (forall color : nat,
          coloring.(Coloring.colors) <= color < length counts ->
          Nth counts color 0).

      Ltac Ok_destruct ok :=
        destruct ok as
          (Ok_instructions &
          Ok_coloring &
          (Ok_length & length_neq_O) &
          Synced_coloring &
          Ok_counts &
          Ok_zero).

      Lemma cons_Down : forall
        (p₀ : Owner.t)
        (x₀ : Instructions.t)
        (coloring : Coloring.t)
        (counts : list nat),
        Ok (Down p₀ :: x₀) coloring counts ->
        exists
          (c₀ : nat)
          (v₀ : nat)
          (v₀' : nat)
          (counts' : list nat),
          Coloring.MapsTo coloring p₀ c₀ /\
          Nth counts c₀ v₀ /\
          Pred v₀ v₀' /\
          Pred.Ok v₀ v₀' /\
          List.Replace.Replace counts c₀ v₀' counts' /\
          Replace.Ok counts c₀ v₀' counts' /\
          Ok x₀ coloring counts'.
      Proof with instructions_tac.
        intros p₀ x₀ coloring counts ok.
        Ok_destruct ok.

        assert (Ok_x₀ : Instructions.Ok x₀) by
          now apply Instructions.Ok.cons_inv with (Down p₀).
        assert (Active_p₀_x : Active p₀ (Down p₀ :: x₀))...
        assert (Absent_p₀_x₀ : Absent p₀ x₀)...

        assert (In_p₀ : Coloring.Contains coloring p₀).
          apply Synced_coloring...
        specialize find_In_Some with (1 := In_p₀) as (c₀ & _ & p₀_to_c₀);
          exists c₀.

        assert (c₀_lt_colors : c₀ < coloring.(Coloring.colors)) by
          now apply Ok_coloring; exists p₀.
        assert (c₀_lt_counts : c₀ < length counts) by
          now apply lt_le_trans with coloring.(Coloring.colors).
        specialize NthError.lt_Some with (1 := c₀_lt_counts) as
          (v₀ & c₀_to_v₀);
          exists v₀.

        unfold ForNth in Ok_counts.
        pose proof Ok_counts as H;
          specialize H with (1 := c₀_to_v₀) as
          (owners₀ & owners₀_iff & owners₀_length).
        assert (p₀_in_owners₀ : M.In p₀ owners₀) by
          now apply owners₀_iff.

        assert (v₀_neq_O : v₀ <> O).
          rewrite <- owners₀_length, <- cardinal_Empty.
          now contradict p₀_in_owners₀.
        specialize Pred.neq_Some with (1 := v₀_neq_O) as
          (v₀' & pred_v₀_v₀' & Ok_v₀_v₀');
          exists v₀'.

        specialize Replace.lt_Some with (x := counts) (1 := c₀_lt_counts) (v := v₀') as
          (counts' & replace_counts' & Ok_counts');
          exists counts'.

        destruct Ok_counts' as (_ & length_counts' & c₀_to_v₀' & H).

        split_left; try assumption.
                now split_left.

              now rewrite <- length_counts'.

            split; intros ?; apply Synced_coloring...

          intros c v' c_to_v'.
          assert (c_lt_counts : c < length counts).
            rewrite length_counts'.
            now apply NthError.Some_lt with v'.
          specialize NthError.lt_Some with (1 := c_lt_counts) as
            (v & c_to_v).
          unfold ForNth in Ok_counts.
          specialize Ok_counts with (1 := c_to_v) as
            (owners & owners_iff & owners_length).
          destruct (Nat.eq_dec c c₀) as [->| c_neq_c₀].
            2: {
              exists owners.
              assert (Some v = Some v') as [= <-] by
                now rewrite <- c_to_v, <- c_to_v'; apply H.
              split; [| assumption].
              intros p.
              rewrite owners_iff, Active.cons_Down_iff by
                assumption.
              enough (Coloring.MapsTo coloring p c -> ~ Owner.eq p₀ p) by tauto.
              intros p_to_c.
              now apply StronglyExtensional with coloring c₀ c;
                [..| change (complement Logic.eq c₀ c)].
            }
            exists (M.remove p₀ owners); split.
              intros p.
              rewrite
                M.remove_spec,
                owners_iff,
                Active.cons_Down_iff by assumption.
              enough ((Owner.eq p₀ p \/ Active p x₀) /\
              ~ Owner.eq p p₀ <-> Active p x₀) by firstorder.
              assert (Owner.eq p₀ p <-> Owner.eq p p₀) as -> by easy.
              enough (Active p x₀ -> ~ Owner.eq p p₀); [tauto|].
              intros Active_p_x₀; contradict Active_p_x₀; rewrite Active_p_x₀...
            change (pred (S (M.cardinal (M.remove p₀ owners))) = v').
            rewrite remove_cardinal_1, owners_length; [| apply owners_iff]...
            enough (Some v = Some v₀ /\ Some v' = Some (pred v₀)) as
              ([= ->] & [= ->]) by reflexivity.
            now rewrite <- c_to_v, <- c_to_v', c₀_to_v₀, c₀_to_v₀', Ok_v₀_v₀'.

          intros c (colors_le_c & c_lt_counts').
          rewrite <- (H c).
            now apply Ok_zero; rewrite length_counts'.
          change (complement Logic.eq c c₀); symmetry.
          now apply Nat.lt_neq, lt_le_trans with coloring.(Coloring.colors).
        Qed.

        Lemma cons_Up : forall
          (p₀ : Owner.t)
          (x₀ : Instructions.t)
          (coloring : Coloring.t)
          (counts : list nat),
          Ok (Up p₀ :: x₀) coloring counts ->
          exists
            (c₀ : nat)
            (v₀ : nat)
            (counts' : list nat),
            let coloring' := add_S coloring p₀ c₀ in
            Min'.Minimum counts c₀ v₀ /\
            Min'.Min counts c₀ v₀ /\
            List.Replace.Replace counts c₀ (S v₀) counts' /\
            Replace.Ok counts c₀ (S v₀) counts' /\
            Ok x₀ coloring' counts'.
        Proof with instructions_tac.
          intros p₀ x₀ coloring counts ok.
          Ok_destruct ok.
          set (labeling := coloring.(Coloring.labeling)) in *.
          set (colors := coloring.(Coloring.colors)) in *.

          assert (Ok_x₀ : Instructions.Ok x₀) by
            now apply Instructions.Ok.cons_inv with (Up p₀).
          assert (Ahead_p₀_x : Ahead p₀ (Up p₀ :: x₀))...
          assert (Active_p₀_x₀ : Active p₀ x₀)...

          assert (counts_neq_nil : counts <> []) by
            now rewrite <- length_zero_iff_nil.

          specialize Min'.neq_Some with (1 := counts_neq_nil) as
            (c₀ & v₀ & Minimum_c₀_v₀ & Min_v₀ & c₀_to_v₀);
            exists c₀, v₀.

          assert (c₀_lt_counts : c₀ < length counts) by
            now apply NthError.Some_lt with v₀.
          assert (c₀_le_colors : c₀ <= colors).
            apply not_gt.
            specialize Nat.nlt_0_r with v₀ as c₀_gt_colors; contradict c₀_gt_colors.
            assert (colors_to_0 : Nth counts colors O) by
              now apply Ok_zero; split; [| transitivity c₀].
            now apply Min_v₀ with (1 := colors_to_0).
          assert (not_In_p₀ : ~ Coloring.Contains coloring p₀).
            apply Synced_coloring...
          assert (max_r : c₀ < colors -> Init.Nat.max (S c₀) colors = colors).
            now intros c₀_lt_colors; apply Nat.max_r.
          assert (max_l : c₀ = colors -> Init.Nat.max (S c₀) colors = S colors).
            now intros ->; apply Nat.max_l, Nat.le_succ_diag_r.

          specialize Replace.lt_Some with (v := S v₀) (1 := c₀_lt_counts) as
            (counts' & -> & _ & length_counts' & c₀_to_S_v₀ & H);
            exists counts'.
          split_left; try easy.
                  apply le_lt_or_eq in c₀_le_colors as
                    [c₀_lt_colors| ->].
                    rewrite max_r; [apply Coloring.Ok.add_lt|]...
                  rewrite max_l; [apply Coloring.Ok.add_eq|]...
                now rewrite <- length_counts'; split; [apply Nat.max_lub|].

              intros p; split.
              intros Active_x₀; apply add_in_iff.
              destruct (Owner.eq_dec p₀ p) as [p₀_eq_p| p₀_neq_p];
                [left| right; apply Synced_coloring]...
              intros Ahead_p.
              apply add_not_in_iff; split.
                contradict Ahead_p; rewrite <- Ahead_p...
              apply Synced_coloring...

            intros c v c_to_v.
            destruct (Nat.eq_dec c c₀) as [->| c_neq_c₀].
              unfold ForNth in Ok_counts.
              specialize Ok_counts with (1 := c₀_to_v₀) as
              (owners & owners_iff & owners_length).

              exists (M.add p₀ owners); split.
                unfold labeling in *.
                simpl in *.

                intro p; destruct (Owner.eq_dec p₀ p) as
                  [p₀_eq_p| p₀_neq_p].
                  symmetry in p₀_eq_p.
                  now rewrite
                    add_eq_iff,
                    add_eq_mapsto_iff,
                    p₀_eq_p.
                now rewrite
                  add_neq_iff,
                  owners_iff,
                  add_neq_mapsto_iff,
                  Active.cons_Up_iff.
              rewrite add_cardinal_2, owners_length.
                now enough (Some (S v₀) = Some v) as [=];
                  [| transitivity (nth_error counts' c₀)].
              rewrite owners_iff.
              enough (~ Active p₀ (Up p₀ :: x₀)) by tauto...
            unfold Count.Ok, ForNth in *.
            specialize Ok_counts with c v as
            (owners & owners_iff & owners_length);
              [now rewrite H|].
            exists owners; split; [| assumption].
            intros p; simpl.
            rewrite owners_iff.
            split; intros (Active_p & p_to_c).
              enough (~ Owner.eq p₀ p).
                apply Active.cons_Up_iff in Active_p.
                now rewrite add_neq_mapsto_iff.
              contradict Active_p; rewrite Active_p...
            apply add_mapsto_iff in p_to_c as
              [(_ & c₀_eq_c)| (p₀_neq_p & p_to_c₀)];
              [now contradict c_neq_c₀|].
            split...

          rewrite <- length_counts'.
          intros c (colors'_le_c₀ & c₀_lt_counts').
          apply le_lt_or_eq in c₀_le_colors as
            [c₀_lt_colors| c₀_eq_colors].
            rewrite max_r in colors'_le_c₀ by assumption; simpl in colors'_le_c₀.
            rewrite <- (H c).
              now apply Ok_zero.
            enough (c₀ <> c) by auto with arith.
            now apply Nat.lt_neq, lt_le_trans with colors.
          rewrite max_l in colors'_le_c₀ by assumption; simpl in colors'_le_c₀.
          rewrite <- (H c).
            apply Ok_zero; auto with arith.
          rewrite c₀_eq_colors.
          enough (colors <> c) by auto with arith.
          now apply Nat.lt_neq.
        Qed.
    End Assumptions.

    Module Type Proposition.
      Parameter t :
        Instructions.t ->
        Coloring.t ->
        list nat ->
        option Coloring.t ->
        Prop.
    End Proposition.

    Module Type BaseCase (P : Proposition).
      Section Basis.
        Variables
          (coloring : Coloring.t)
          (counts : list nat).

        Parameter nil :
          Assumptions.Ok [] coloring counts ->
          P.t [] coloring counts (Some coloring).
      End Basis.
    End BaseCase.

    Module Type InductionSteps (P : Proposition).
      Section Steps.
        Variables
          (p₀ : Owner.t)
          (x₀ : Instructions.t)
          (coloring : Coloring.t)
          (counts counts' : list nat)
          (c₀ v₀ v₀' : nat)
          (result : option Coloring.t).

        Parameter cons_Up :
          Assumptions.Ok (Up p₀ :: x₀) coloring counts ->
          Min'.Min counts c₀ v₀ ->
          List.Replace.Ok counts c₀ (S v₀) counts' ->
          P.t x₀ (add_S coloring p₀ c₀) counts' result ->
          P.t (Up p₀ :: x₀) coloring counts result.

        Parameter cons_Down :
          Assumptions.Ok (Down p₀ :: x₀) coloring counts ->
          Pred.Ok v₀ v₀' ->
          List.Replace.Ok counts c₀ v₀' counts' ->
          P.t x₀ coloring counts' result ->
          P.t (Down p₀ :: x₀) coloring counts result.
      End Steps.
    End InductionSteps.

    Module Type Steps := Proposition <+ BaseCase <+ InductionSteps. (* TODO *)

    Module InductionPrinciple (P : Proposition) (B : BaseCase P) (S : InductionSteps P).
      Lemma ind :
        forall
          (instructions : Instructions.t)
          (coloring : Coloring.t)
          (counts : list nat),
          Assumptions.Ok
            instructions
            coloring
            counts ->
          P.t
            instructions
            coloring
            counts
            (fixed_body instructions coloring counts).
      Proof.
        induction instructions as [| ([|] & p₀) x₀ IHx₀];
          intros coloring counts ok.
            now apply B.nil.
          simpl; unfold bind.
          specialize Assumptions.cons_Up with (1 := ok) as
            (c₀ & v₀ & counts' & -> & Ok_c₀_v₀ & -> & Ok_counts' & ok').
          specialize IHx₀ with (1 := ok').
          now apply S.cons_Up with counts' c₀ v₀.
        simpl; unfold bind.
        specialize (Assumptions.cons_Down) with (1 := ok) as
          (c₀ & v₀ & v₀' & counts' & p₀_to_c₀ & H).
        rewrite Map.find_1 with (1 := p₀_to_c₀).
        destruct H as (-> & -> & ? & -> & Ok_counts' & ok').
        specialize IHx₀ with (1 := ok').
        now apply S.cons_Down with counts' c₀ v₀ v₀'.
      Qed.
    End InductionPrinciple.
  End Fixed.
End Make.

Set Implicit Arguments.

Require Import
  Coq.Arith.Arith
  Coq.Lists.List
  Coq.Lists.SetoidList
  Coq.Structures.Equalities.

Import ListNotations.

Require Import
  Shuffle.Misc
  Shuffle.List.

Import
  Misc(bind).

Require Import
  Coq.Classes.RelationPairs
  Coq.Classes.RelationClasses
  Coq.Classes.Morphisms.

Module Setoid.

  Section Instances.
    Context
      (A : Type)
      (Eq_A : relation A)
      (B : Type)
      (Eq_B : relation B).

    Definition eqprodAB :=
      RelProd Eq_A Eq_B.

    #[local]
    Instance Prod_Reflexive
      {Reflexive_A : Reflexive Eq_A}
      {Reflexive_B : Reflexive Eq_B} :
      Reflexive eqprodAB.
    Proof.
      unfold eqprodAB; auto with typeclass_instances.
    Qed.

    #[local]
    Instance Prod_PartialSetoid
      {PartialSetoid_A : PER Eq_A}
      {PartialSetoid_B : PER Eq_B} :
      PER eqprodAB.
    Proof.
      split.
        intros x y (x₁_eq_y₁ & x₂_eq_y₂); now split; symmetry.
      intros x y z (x₁_eq_y₁ & x₂_eq_y₂) (y₁_eq_z₁ & y₂_eq_z₂);
      split; now transitivity y.
    Qed.

    #[local]
    Instance Prod_Setoid
      {Setoid_A : Equivalence Eq_A}
      {Setoid_B : Equivalence Eq_B} :
      Equivalence eqprodAB.
    Proof.
      split; [apply Prod_Reflexive| apply Prod_PartialSetoid..].
    Qed.

    Inductive eqsumAB
      (A : Type)
      (R : A -> A -> Prop)
      (B : Type)
      (S : B -> B -> Prop) :
      A + B ->
      A + B ->
      Prop :=
      | Left_Left :
          forall
          x y : A,
          R x y ->
          eqsumAB R S (inl x) (inl y)
      | Right_Right :
          forall
          x y : B,
          S x y ->
          eqsumAB R S (inr x) (inr y).

    #[local]
    Instance Sum_Reflexive
      {Reflexive_A : Reflexive Eq_A}
      {Reflexive_B : Reflexive Eq_B} :
      Reflexive (eqsumAB Eq_A Eq_B).
    Proof.
      intros [x₁| x₂]; constructor; reflexivity.
    Qed.

    #[local]
    Instance Sum_PartialSetoid
      {PartialSetoid_A : PER Eq_A}
      {PartialSetoid_B : PER Eq_B} :
      PER (eqsumAB Eq_A Eq_B).
    Proof.
      split.
        intros [x₁| x₂] [y₁| y₂] x_eq_y;
        inversion_clear x_eq_y as [? ? x₁_eq_y₁| ? ? x₂_eq_y₂];
        now constructor; symmetry.
      intros [x₁| x₂] [y₁| y₂] [z₁| z₂] x_eq_y y_eq_z;
      inversion_clear x_eq_y as [? ? x₁_eq_y₁| ? ? x₂_eq_y₂];
      inversion_clear y_eq_z as [? ? y₁_eq_z₁| ? ? y₂_eq_z₂];
      constructor; [transitivity y₁| transitivity y₂]; assumption.
    Defined.

    #[local]
    Instance Sum_Setoid
      {Setoid_A : Equivalence Eq_A}
      {Setoid_B : Equivalence Eq_B} :
      Equivalence (eqsumAB Eq_A Eq_B).
    Proof.
      split; [apply Sum_Reflexive| apply Sum_PartialSetoid..]; exact _.
    Qed.

    Inductive eqoptionA
      (A : Type)
      (R : A -> A -> Prop) :
      option A ->
      option A ->
      Prop :=
      | Some_Some :
          forall
          x y : A,
          R x y ->
          eqoptionA R (Some x) (Some y)
      | None_None :
          eqoptionA R None None.

    #[local]
    Instance Option_Reflexive
      {Reflexive_A : Reflexive Eq_A} :
      Reflexive (eqoptionA Eq_A).
    Proof.
      intros [x|]; now constructor.
    Qed.

    #[local]
    Instance Option_PartialSetoid
      {PartialSetoid_A : PER Eq_A} :
      PER (eqoptionA Eq_A).
    Proof.
      split.
        intros x y [x' y' x_eq_y|]; constructor.
        now symmetry.
      intros x y [z|] [x' y' x_eq_y|] y_eq_z; inversion_clear y_eq_z; constructor.
      now transitivity y'.
    Qed.

    #[local]
    Instance Option_Setoid
      {Setoid_A : Equivalence Eq_A} :
      Equivalence (eqoptionA Eq_A).
    Proof.
      split; [apply Option_Reflexive| apply Option_PartialSetoid..]; exact _.
    Qed.

    #[local]
    Instance List_Reflexive
      {Reflexive_A : Reflexive Eq_A} :
      Reflexive (eqlistA Eq_A).
    Proof.
      intros x; induction x as [| u₀ x₀ IHx₀]; now constructor.
    Qed.

    #[local]
    Instance List_PartialSetoid
      {PartialSetoid_A : PER Eq_A} :
      PER (eqlistA Eq_A).
    Proof.
      split.
        intros x y x_eq_y; induction x_eq_y as [| u₀ v₀ x₀ y₀ IHx₀y₀];
        now constructor.
      intros x y z x_eq_y; revert z;
      induction x_eq_y as [| u₀ v₀ x₀ y₀ u₀_eq_v₀ x₀_eq_y₀ IHx₀_eq_y₀];
      intros z y_eq_z; [assumption|].
      destruct z as [| w₀ z₀];
      inversion_clear y_eq_z as [| ? ? ? ? v₀_eq_w₀ y₀_eq_z₀].
      now constructor; [transitivity v₀| apply IHx₀_eq_y₀].
    Qed.

    #[local]
    Instance List_Setoid
      {Setoid_A : Equivalence Eq_A} :
      Equivalence (eqlistA Eq_A).
    Proof.
      split; [apply List_Reflexive| apply List_PartialSetoid..]; exact _.
    Qed.

    #[local]
    Instance Arrow_PartialSetoid
      {PartialSetoid_A : PER Eq_A}
      {PartialSetoid_B : PER Eq_B} :
      PER (Eq_A ==> Eq_B).
    Proof.
      now apply respectful_per.
    Qed.
  End Instances.

  Section Misc.
    Context
      (A : Type)
      (Eq_A : relation A)
      (B : Type)
      (Eq_B : relation B).

    Definition if_then_else
      (b : bool)
      (x y : A) :
      A :=
      if b then x else y.

    #[local]
    Instance Morphism_if_then_else :
      Proper (Logic.eq ==> Eq_A ==> Eq_A ==> Eq_A) if_then_else.
    Proof.
      intros b b' <- x x' x_eq_x' y y' y_eq_y'.
      now destruct b.
    Qed.

    #[local]
    Instance Morphism_pair :
      Proper (Eq_A ==> Eq_B ==> eqprodAB Eq_A Eq_B) (@pair A B).
    Proof.
      intros x x' x_eq_x' y y' y_eq_y'.
      now split.
    Qed.

    #[local]
    Instance Morphism_inl :
      Proper (Eq_A ==> eqsumAB Eq_A Eq_B) (@inl A B).
    Proof.
      intros x x' x_eq_x'; now constructor.
    Qed.

    #[local]
    Instance Morphism_inr :
      Proper (Eq_B ==> eqsumAB Eq_A Eq_B) (@inr A B).
    Proof.
      intros y y' y_eq_y'; now constructor.
    Qed.

    #[local]
    Instance Morphism_Some :
      Proper (Eq_A ==> eqoptionA Eq_A) (@Some A).
    Proof.
      intros x y x_eq_y.
      now constructor.
    Qed.

    #[local]
    Instance Morphism_option_map :
      Proper ((Eq_A ==> Eq_B) ==> eqoptionA Eq_A ==> eqoptionA Eq_B) (@option_map A B).
    Proof.
      intros f g f_eq_g [x|] [x'|] x_eq_x'; inversion_clear x_eq_x';
      constructor; now apply f_eq_g.
    Qed.

    #[local]
    Instance Morphism_option_map_pointwise :
      Proper (pointwise_relation A Eq_B ==> eq ==> eqoptionA Eq_B) (@option_map A B).
    Proof.
      intros f f' f_eq_f' x x' <-.
      destruct x as [x|]; constructor.
      apply f_eq_f'.
    Qed.

    #[local]
    Instance Morphism_bind :
      Proper (eqoptionA Eq_A ==> (Eq_A ==> eqoptionA Eq_B) ==> eqoptionA Eq_B) (@bind A B).
    Proof.
      intros x x' x_eq_x' f f' f_eq_f'.
       destruct x_eq_x' as [x x' x_eq_x'|].
        now apply f_eq_f'.
      constructor.
    Qed.

    #[local]
    Instance Morphism_bind_pointwise :
      Proper (eq ==> pointwise_relation A (eqoptionA Eq_B) ==> eqoptionA Eq_B) (@bind A B).
    Proof.
      intros x x' <- f f' f_eq_f'.
      destruct x as [x|].
        now apply f_eq_f'.
      constructor.
    Qed.

    Fixpoint try_fold
      (init : B)
      (f : B -> A -> option B)
      (x : list A) :
      option B :=
      match x with
      | [] =>
          Some init
      | u₀ :: x₀ =>
          match try_fold init f x₀ with
          | Some t₁ => f t₁ u₀
          | None => None
          end
      end.

    #[local]
    Instance Morphism_try_fold :
      Proper (Eq_B ==> (Eq_B ==> Eq_A ==> eqoptionA Eq_B) ==> eqlistA Eq_A ==> eqoptionA Eq_B) try_fold.
    Proof.
      intros init init' init_eq_init' f f' f_eq_f' x x' x_eq_x'.
      induction x_eq_x' as [| u₀ u₀' x₀ x₀' u₀_eq_u₀' x₀_eq_x₀' IHx₀_eq_x₀'].
        now constructor.
      simpl.
      destruct (try_fold init f x₀) as [t₁|], (try_fold init' f' x₀') as [t₁'|];
      inversion_clear IHx₀_eq_x₀' as [? ? t₁_eq_t₁'|].
        now apply f_eq_f'.
      constructor.
    Qed.

    #[local]
    Instance Morphism_cons :
      Proper (Eq_A ==> eqlistA Eq_A ==> eqlistA Eq_A) (@cons A).
    Proof.
      intros u u' u_eq_u' x x' x_eq_x'.
      now constructor.
    Qed.

    #[local]
    Instance Morphism_InA
      {Setoid_A : Equivalence Eq_A} :
      Proper (Eq_A ==> eqlistA Eq_A ==> iff) (@InA A Eq_A).
    Proof.
      intros v v' v_eq_v' x x' x_eq_x'.
      induction x_eq_x' as
        [| u₀ u₀' x₀ x₀' u₀_eq_u₀' x₀_eq_x₀' IHx₀_eq_x₀'].
        now rewrite 2 ! InA_nil.
      now rewrite 2 ! InA_cons, IHx₀_eq_x₀', v_eq_v', u₀_eq_u₀'.
    Qed.

    #[local]
    Instance Morphism_eq
      {PartialSetoid_A : PER Eq_A} :
      Proper (Eq_A ==> Eq_A ==> iff) Eq_A.
    Proof.
      now apply PER_morphism.
    Qed.
  End Misc.
End Setoid.
Import Setoid.

Module Label.
  Class Signature
    (L : Type)
    (Eq_L : relation L) :
    Type :=
    {
      Ok :
        list L ->
        Prop;
      Morphism_Ok :>
        Proper (eqlistA Eq_L ==> iff) Ok;
    }.
  Arguments Ok {L} {Eq_L} _.

  Class Theory
    (L : Type)
    (Eq_L : relation L)
    (Signature_L : @Signature L Eq_L) :
    Prop :=
    {
      Ok_tl_morphism :
        forall
        (u₀ : L)
        (x₀ : list L),
        Signature_L.(Ok) (u₀ :: x₀) ->
        Signature_L.(Ok) x₀;
    }.
End Label.

Module Relational.
  Section Relational.
    Class Signature
      (L : Type)
      (Eq_L : relation L)

      (S : Type)
      (Eq_S : relation S) :
      Type :=
      {
        Initial :
          S ->
          Prop;
        Morphism_Initial :>
          Proper (Eq_S ==> iff) Initial;
        Transition :
          S ->
          L ->
          S ->
          Prop;
        Morphism_Transition :>
          Proper (Eq_S ==> Eq_L ==> Eq_S ==> iff) Transition;
        Ok :
          list L ->
          S ->
          Prop;
        Morphism_Ok :>
          Proper (eqlistA Eq_L ==> Eq_S ==> iff) Ok;
      }.
    #[global]
    Arguments Initial {L} {Eq_L} {S} {Eq_S} _.
    #[global]
    Arguments Transition {L} {Eq_L} {S} {Eq_S} _.
    #[global]
    Arguments Ok {L} {Eq_L} {S} {Eq_S} _.

    Context
      (L : Type)
      (Eq_L : relation L)
      (Signature_L : @Label.Signature L Eq_L).

    Class Theory
      (S : Type)
      (Eq_S : relation S)
      (Signature_S : @Signature L Eq_L S Eq_S) :
      Prop :=
      {
        Ok_Initial :
          forall
          s : S,
          Signature_S.(Initial) s ->
          Signature_S.(Ok) [] s;
        executable :
          forall
          (u₀ : L)
          (x₀ : list L)
          (s : S),
          Signature_L.(Label.Ok) (u₀ :: x₀) ->
          Signature_S.(Ok) x₀ s ->
          exists t : S,
          Signature_S.(Transition) s u₀ t /\
          Signature_S.(Ok) (u₀ :: x₀) t;
      }.

    Context
      (S : Type)
      (Eq_S : relation S)
      (Signature_S : @Signature L Eq_L S Eq_S)

      (S' : Type)
      (Eq_S' : relation S')
      (Signature_S' : @Signature L Eq_L S' Eq_S')

      (h : S -> S').

    Class WeaklyReflectiveHomomorphism :
      Prop :=
      {
        Setoid_Morphism :>
          Proper (Eq_S ==> Eq_S') h;
        Preserves_Initial :
          forall
          s : S,
          Signature_S.(Initial) s ->
          Signature_S'.(Initial) (h s);
        Preserves_Transition :
          forall
          (s : S)
          (u : L)
          (t : S),
          Signature_S.(Transition) s u t ->
          Signature_S'.(Transition) (h s) u (h t);
        Preserves_Ok :
          forall
          (x : list L)
          (s : S),
          Signature_S.(Ok) x s ->
          Signature_S'.(Ok) x (h s);
        Weakly_Initial :
          forall
          s : S,
          Signature_S'.(Initial) (h s) ->
          exists
          s' : S,
          Eq_S' (h s) (h s') /\
          Signature_S.(Initial) s';
        Weakly_Ok :
          forall
          (x : list L)
          (s : S),
          Signature_S'.(Ok) x (h s) ->
          exists
          s' : S,
          Eq_S' (h s) (h s') /\
          Signature_S.(Ok) x s';
      }.

    #[program]
    Definition Signature_Image
      {Morphism_h : Proper (Eq_S ==> Eq_S') h} :
      Signature Eq_L Eq_S :=
      {|
        Initial s :=
          Signature_S'.(Initial) (h s);
        Transition s u t:=
          Signature_S'.(Transition) (h s) u (h t);
        Ok x s :=
          Signature_S'.(Ok) x (h s);
      |}.
    Next Obligation.
      intros x x' x_eq_x'.
      now apply Morphism_Initial, Morphism_h.
    Qed.
    Next Obligation.
      intros x x' x_eq_x' u u' u_eq_u' y y' y_eq_y'.
      now apply Morphism_Transition with (2 := u_eq_u'); apply Morphism_h.
    Qed.
    Next Obligation.
      intros l l' l_eq_l' x x' x_eq_x'.
      now apply Morphism_Ok, Morphism_h.
    Qed.

    #[local]
    Instance Theory_Image
      {Reflexive_L : Reflexive Eq_L}
      {Setoid_S : Equivalence Eq_S}
      {Theory_S : Theory Signature_S}
      {Homomorphism_h : WeaklyReflectiveHomomorphism} :
      Theory Signature_Image.
    Proof.
      split; simpl.
        intros x Initial_h_x.
         apply Weakly_Initial in Initial_h_x as
          (x' & h_x_eq_h_x' & Initial_x').
        apply Morphism_Ok with [] (h x').
            constructor.
          assumption.
        now apply Preserves_Ok, Ok_Initial.
      intros u₀ x₀ s Ok_x Ok_x₀_h_s.
      apply Weakly_Ok in Ok_x₀_h_s as (s' & h_s_eq_h_s' & Ok_x₀_s').
      specialize @executable with (2 := Ok_x) (3 := Ok_x₀_s') as
        (t' & Transition_s'_u₀_t' & Ok_x_t').
        exact _.
      exists t'; split.
        apply Morphism_Transition with (h s') u₀ (h t').
              assumption.
            reflexivity.
          now apply @Setoid_Morphism with (1 := Homomorphism_h).
        now apply Preserves_Transition.
      now apply Preserves_Ok.
    Qed.
  End Relational.

  Module Path.
    Section Path.
      Class Signature
        (L S : Type) :
        Type :=
        {
          Path :
            S ->
            list L ->
            S ->
            Prop;
        }.
      #[global]
      Arguments Path {L} {S} _.

      Context
        (L : Type)
        (Eq_L : relation L)
        (Label_Signature_L : @Label.Signature L Eq_L)

        (S : Type)
        (Eq_S : relation S)
        (Relational_Signature_L_S : @Relational.Signature L Eq_L S Eq_S).

      Class Theory
        (Signature_L_S : Signature L S) :
        Prop :=
        {
          nil_iff :
            forall
            s t : S,
            Signature_L_S.(Path) s [] t <->
            Eq_S s t;
          cons_iff :
            forall
            (u₀ : L)
            (x₀ : list L)
            (s t₀ : S),
            Signature_L_S.(Path) s (u₀ :: x₀) t₀ <->
            (exists
            t₁ : S,
            Signature_L_S.(Path) s x₀ t₁ /\
            Relational_Signature_L_S.(Transition) t₁ u₀ t₀);
        }.

      Inductive R
        (s : S) :
        list L ->
        S ->
        Prop :=
        | Nil :
            forall
            t : S,
            Eq_S s t ->
            R s [] t
        | Cons :
            forall
            (u₀ : L)
            (x₀ : list L)
            (t₀ t₁ : S),
            R s x₀ t₁ ->
            Relational_Signature_L_S.(Transition) t₁ u₀ t₀ ->
            R s (u₀ :: x₀) t₀.

      #[local, program]
      Instance Theory_R :
        Theory
          {|
            Path :=
              R;
          |}.
      Next Obligation.
        now split; [inversion 1| constructor].
      Qed.
      Next Obligation.
        split.
          inversion_clear 1 as [| ? ? ? t₁ Transition_s_t₁ Transition_t₁_t₀].
          now exists t₁.
        intros (t₁ & Transition_s_t₁ & Transition_t₁_t₀).
        now constructor 2 with t₁.
      Qed.

      Context
        (Signature_L_S : Signature L S)
        {Theory_L_S : Theory Signature_L_S}.

      Definition nil :
        forall
        s t : S,
        Eq_S s t ->
        Signature_L_S.(Path) s [] t.
      Proof.
        apply nil_iff.
      Qed.

      Definition cons :
        forall
        (s : S)
        (u₀ : L)
        (x₀ : list L)
        (t₀ t₁ : S),
        Signature_L_S.(Path) s x₀ t₁ ->
        Relational_Signature_L_S.(Transition) t₁ u₀ t₀ ->
        Signature_L_S.(Path) s (u₀ :: x₀) t₀.
      Proof.
        intros s u₀ x₀ t₀ t₁ Path_s_x₀_t₁ Transition_t₁_u₀_t₀.
        now apply cons_iff; exists t₁.
      Qed.

      Context
        {Reflexive_L : Reflexive Eq_L}
        {Setoid_S : Equivalence Eq_S}.

      #[local]
      Instance Morphism_Path :
        Proper (Eq_S ==> eqlistA Eq_L ==> Eq_S ==> iff) Signature_L_S.(Path).
      Proof.
        intros s s' s_eq_s' x x' x_eq_x'.
        induction x_eq_x' as [| u₀ u₀' x₀ x₀' u₀_eq_u₀' x₀_eq_x₀' IHx₀_eq_x₀'];
          intros t t' t_eq_t'.
          now rewrite 2!nil_iff, s_eq_s', t_eq_t'.
        rewrite 2!cons_iff.
        enough (forall
          t₁ : S,
          Signature_L_S.(Path) s x₀ t₁ /\ Relational_Signature_L_S.(Transition) t₁ u₀ t <->
          Signature_L_S.(Path) s' x₀' t₁ /\ Relational_Signature_L_S.(Transition) t₁ u₀' t') by firstorder.
        intros t₁; specialize (IHx₀_eq_x₀' t₁ t₁ (reflexivity t₁)).
        enough (
          Relational_Signature_L_S.(Transition) t₁ u₀ t <->
          Relational_Signature_L_S.(Transition) t₁ u₀' t') by
          firstorder.
        now apply Morphism_Transition.
      Qed.

      #[local]
      Existing Instance List_Reflexive.
      Lemma app_iff :
        forall
        (x y : list L)
        (s u : S),
        Signature_L_S.(Path) s (x ++ y) u <->
        exists
        t : S,
        Signature_L_S.(Path) s y t /\
        Signature_L_S.(Path) t x u.
      Proof.
        intros x y s; move x after s.
        induction x as [| u₀ x₀ IHx₀]; intros u.
          setoid_rewrite nil_iff.
          split.
            intros Transition_s_y_u; now exists u.
          intros (t & Transition_s_y_t & t_eq_u).
          now rewrite <- t_eq_u.
        setoid_rewrite cons_iff; setoid_rewrite IHx₀; firstorder.
      Qed.

      Context
        {Label_Theory_L : Label.Theory Label_Signature_L}
        {Relational_Theory_L_S : Relational.Theory Label_Signature_L Relational_Signature_L_S}.

      Lemma executable :
        forall
        (x y : list L)
        (s : S),
        Label_Signature_L.(Label.Ok) (x ++ y) ->
        Relational_Signature_L_S.(Ok) y s ->
        exists t : S,
        Signature_L_S.(Path) s x t /\
        Relational_Signature_L_S.(Ok) (x ++ y) t.
      Proof.
        intros x y s Ok_x_app_y Ok_y_s; move x at bottom.
        induction x as [| u₀ x₀ IHx₀].
          now exists s; split; [apply nil|].
        specialize IHx₀ as (t₁ & Path_s_t₁ & Ok_x₀_app_y_t₁).
          now apply Label.Ok_tl_morphism with u₀.
        specialize (executable u₀ (x₀ ++ y) t₁) as
          (t₀ & Transition_t₁_t₀ & Ok_x_app_y_t₀); [assumption..|].
        now exists t₀; split; [apply cons with t₁|].
      Qed.

      Lemma executable_Initial :
        forall
        (x : list L)
        (s : S),
        Label_Signature_L.(Label.Ok) x ->
        Relational_Signature_L_S.(Initial) s ->
        exists
        t : S,
        Signature_L_S.(Path) s x t /\
        Relational_Signature_L_S.(Ok) x t.
      Proof.
        intros x s Ok_x InitialState_s.
        specialize (executable x [] s) as (t & Path_s_t & Ok_x_t).
            now rewrite app_nil_r.
          now apply Ok_Initial with Label_Signature_L.
        now rewrite app_nil_r in Ok_x_t; exists t.
      Qed.
    End Path.
  End Path.
End Relational.

Module Algebraic.
  Section Algebraic.
    Class Signature
      (L : Type)
      (Eq_L : relation L)

      (S : Type)
      (Eq_S : relation S) :
      Type :=
      {
        init :
          S;
        f :
          S ->
          L ->
          option S;
        Morphism_f :>
          Proper (Eq_S ==> Eq_L ==> eqoptionA Eq_S) f;
        Ok :
          list L ->
          S ->
          Prop;
        Morphism_Ok :>
          Proper (eqlistA Eq_L ==> Eq_S ==> iff) Ok;
      }.
    #[global]
    Arguments init {L} {Eq_L} {S} {Eq_S} _.
    #[global]
    Arguments f {L} {Eq_L} {S} {Eq_S} _.
    #[global]
    Arguments Ok {L} {Eq_L} {S} {Eq_S} _.

    Context
      (L : Type)
      (Eq_L : relation L)
      (Signature_L : @Label.Signature L Eq_L).


    #[local]
    Existing Instance Option_Setoid.
    #[local]
    Existing Instance Morphism_Some.
    #[program]
    Definition to_Relational_Signature
      (S : Type)
      (Eq_S : relation S)
      (Signature_S : @Signature L Eq_L S Eq_S)

      {Setoid_S : Equivalence Eq_S} :
      @Relational.Signature L Eq_L S Eq_S :=
      {|
        Relational.Initial x :=
          Eq_S x Signature_S.(init);
        Relational.Transition s u t :=
          eqoptionA Eq_S (Signature_S.(f) s u) (Some t);
        Relational.Ok :=
          Signature_S.(Ok);
      |}.
    Next Obligation.
      now intros x x' ->.
    Qed.
    Next Obligation.
      intros s s' s_eq_s' u u' u_eq_u' t t' t_eq_t'; rewrite t_eq_t'.
      split.
        intros f_s_u_eq_t.
        now transitivity (Signature_S.(f) s u); [symmetry; apply Morphism_f|].
      intros f_s'_u'_eq_t'.
      now transitivity (Signature_S.(f) s' u'); [apply Morphism_f|].
    Qed.

    Class Theory
      (S : Type)
      (Eq_S : relation S)
      (Signature_S : @Signature L Eq_L S Eq_S) :
      Prop :=
      {
        Ok_init :
          Signature_S.(Ok) [] Signature_S.(init);
        executable :
          forall
          (u₀ : L)
          (x₀ : list L)
          (s : S),
          Signature_L.(Label.Ok) (u₀ :: x₀) ->
          Signature_S.(Ok) x₀ s ->
          exists t : S,
          eqoptionA Eq_S (Signature_S.(f) s u₀) (Some t) /\
          Signature_S.(Ok) (u₀ :: x₀) t;
      }.

    Context
      (S : Type)
      (Eq_S : relation S)
      (Signature_S : @Signature L Eq_L S Eq_S)

      (S' : Type)
      (Eq_S' : relation S')
      (Signature_S' : @Signature L Eq_L S' Eq_S')

      (h : S -> S').

    Class WeaklyReflectiveHomomorphism :
      Prop :=
      {
        Setoid_Morphism :>
          Proper (Eq_S ==> Eq_S') h;
        Preserves_init :
          Eq_S' (Signature_S'.(init)) (h Signature_S.(init));
        Preserves_f :
          forall
          (s : S)
          (u : L),
          eqoptionA Eq_S' (Signature_S'.(f) (h s) u) (option_map h (Signature_S.(f) s u));
        Preserves_Ok :
          forall
          (x : list L)
          (s : S),
          Signature_S.(Ok) x s ->
          Signature_S'.(Ok) x (h s);
        Weakly_Ok :
          forall
          (x : list L)
          (s : S),
          Signature_S'.(Ok) x (h s) ->
          exists
          s' : S,
          Eq_S' (h s) (h s') /\
          Signature_S.(Ok) x s';
      }.

    #[program]
    Definition Signature_Image
      {Morphism_h : Proper (Eq_S ==> Eq_S') h} :
      @Signature L Eq_L S Eq_S :=
      {|
        init :=
          Signature_S.(init);
        f :=
          Signature_S.(f);
        Ok x s :=
          Signature_S'.(Ok) x (h s);
      |}.
    Next Obligation.
      intros l l' l_eq_l' x x' x_eq_x'.
      now apply Morphism_Ok, Morphism_h.
    Qed.

    #[local]
    Existing Instance Morphism_option_map.
    #[local]
    Existing Instance List_Reflexive.
    #[local]
    Instance Theory_Image
      {Reflexive_L : Reflexive Eq_L}
      {Setoid_S : Equivalence Eq_S}
      {Theory_S : Theory Signature_S}
      {Setoid_S' : Equivalence Eq_S'}
      {Homomorphism_h : WeaklyReflectiveHomomorphism} :
      Theory Signature_Image.
    Proof.
      split; simpl.
        apply Preserves_Ok, Ok_init.
      intros u₀ x₀ s Ok_x Ok'_x₀_h_s.
      apply Weakly_Ok in Ok'_x₀_h_s as (s' & h_s_eq_h_s' & Ok_x₀_s').
      specialize (executable u₀ x₀ s' Ok_x Ok_x₀_s') as
        (t' & f_s'_u₀_eq_t' & Ok_x_t').
      assert (H : eqoptionA Eq_S' (option_map h (Signature_S.(f) s u₀)) (option_map h (Some t'))).
        now rewrite <- Preserves_f, h_s_eq_h_s', Preserves_f, f_s'_u₀_eq_t'.
      destruct (Signature_S.(f) s u₀) as [t|]; inversion_clear H.
      exists t; split; [reflexivity|].
      now apply Morphism_Ok with (u₀ :: x₀) (h t'); [..| apply Preserves_Ok].
    Qed.

    #[local]
    Instance to_Relational_Theory
      {Setoid_S : Equivalence Eq_S}
      {Theory_S : Theory Signature_S} :
      @Relational.Theory L Eq_L Signature_L S Eq_S (@to_Relational_Signature S Eq_S Signature_S Setoid_S).
    Proof.
      split.
        intros s s_eq_init.
        apply Morphism_Ok with [] (Signature_S.(init)).
            constructor.
          assumption.
        exact Ok_init.
      intros u₀ x₀ s Ok_x Ok_x₀_s.
      now apply executable.
    Qed.

    Definition to_Relational_WeaklyReflectiveHomomorphism
      {Setoid_S : Equivalence Eq_S}
      {Setoid_S' : Equivalence Eq_S'}
      {Homomorphism_h : WeaklyReflectiveHomomorphism} :
      Relational.WeaklyReflectiveHomomorphism
        (to_Relational_Signature Signature_S)
        (to_Relational_Signature Signature_S')
        h.
    Proof.
      split; simpl.
                exact _.
              intros s s_eq_init.
              transitivity (h Signature_S.(init)).
                now apply @Setoid_Morphism with (1 := Homomorphism_h).
              symmetry; apply Preserves_init.
            intros s u t Transition_s_u_t.
            now rewrite Preserves_f, Transition_s_u_t.
          intros x s; apply Preserves_Ok.
        intros s h_s_eq_init.
        exists (Signature_S.(init)); split.
          rewrite h_s_eq_init; apply Preserves_init.
        reflexivity.
      intros x s; apply Weakly_Ok.
    Qed.

    Definition to_Relational_Path_Signature :
      Relational.Path.Signature L S :=
      {|
        Relational.Path.Path s x t :=
          eqoptionA Eq_S (try_fold s Signature_S.(f) x) (Some t);
      |}.

    #[local, program]
    Instance to_Relational_Path_Theory
      {Reflexive_L : Reflexive Eq_L}
      {Setoid_S : Equivalence Eq_S} :
      Relational.Path.Theory
        (to_Relational_Signature Signature_S)
        to_Relational_Path_Signature.
    Next Obligation.
      now split; intros s_eq_t; [inversion_clear s_eq_t| rewrite s_eq_t].
    Qed.
    Next Obligation.
      destruct (try_fold s (Signature_S.(f)) x₀) as [t₁|].
        split.
          intros f_t₁_u₀_eq_t₀; exists t₁; now split.
        intros (t₁' & Some_t₁_eq_Some_t₁' & f_t₁'_u₀_eq_t₀);
        inversion_clear Some_t₁_eq_Some_t₁' as [? ? t₁_eq_t₁'|].
        now rewrite t₁_eq_t₁'.
      split.
        intros None_eq_Some_t₀; inversion None_eq_Some_t₀.
      intros (t₁ & None_eq_Some_t₁ & _); inversion_clear None_eq_Some_t₁.
    Qed.
  End Algebraic.
End Algebraic.

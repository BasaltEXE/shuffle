Require Import
  Coq.Arith.Arith
  Coq.Lists.List
  Coq.Lists.SetoidList
  Coq.Structures.Equalities.

Import ListNotations.

Require Import
  Shuffle.List.

Require Import
  Coq.Classes.RelationClasses
  Coq.Classes.Morphisms.

Module Setoid.
  Class Eq
    (A : Type) :
    Type :=
    eq :
      A ->
      A ->
      Prop.

  Class PartialSetoid
    (A : Type)
    {Eq_A : Eq A} :
    Prop :=
    partial_setoid_per :>
      PER (@eq A Eq_A).

  Class Setoid
    (A : Type)
    {Eq_A : Eq A} :
    Prop :=
    setoid_equivalence :>
      Equivalence (@eq A Eq_A).

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
        eqoptionA A R (Some x) (Some y)
    | None_None :
        eqoptionA A R None None.

  Instance Option_Eq
    (A : Type)
    {Eq_A : Eq A} :
    Eq (option A) :=
    eqoptionA A (@eq A Eq_A).

  Instance Option_Setoid
    (A : Type)
    {Eq_A : Eq A}
    {Setoid_A : Setoid A} :
    Setoid (option A).
  Proof.
    split.
        intros [x|]; now constructor.
      intros x y [x' y' x_eq_y|]; constructor.
      now symmetry.
    intros x y [z|] [x' y' x_eq_y|] y_eq_z; inversion_clear y_eq_z; constructor.
    now transitivity y'.
  Qed.

  Add Parametric Morphism
    (A : Type)
    {Eq_A : Eq A} :
    (@Some A) with signature
    (eq ==> eq) as
    Some_morphism.
  Proof.
    intros x y x_eq_y.
    now constructor.
  Qed.

  Add Parametric Morphism
    (A B : Type)
    {Eq_A : Eq A}
    {Eq_B : Eq B}  :
    (@option_map A B) with signature
    ((eq ==> eq) ==> eq ==> eq) as
    option_map_morphism.
  Proof.
    intros f g f_eq_g [x|] [x'|] x_eq_x'; inversion_clear x_eq_x'; constructor.
    now apply f_eq_g.
  Qed.

  Instance List_Eq
    (A : Type)
    {Eq_A : Eq A} :
    Eq (list A) :=
    eqlistA eq.

  Instance Proposition_Eq :
    Eq Prop :=
    iff.

  Instance Arrow_Eq
    (A B : Type)
    {Eq_A : Eq A}
    {Eq_B : Eq B} :
    Eq (A -> B) :=
    (eq ==> eq)%signature.

  Instance Arrow_PartialSetoid
    (A B : Type)
    {Eq_A : Eq A}
    {Eq_B : Eq B}
    {PartialSetoid_A : PartialSetoid A}
    {PartialSetoid_B : PartialSetoid B} :
    PartialSetoid (A -> B).
  Proof.
    now apply respectful_per.
  Qed.

  Class Morphism
    {A : Type}
    {Eq_A : Eq A}
    (f : A) :
    Prop :=
    Preserves_eq :>
      Proper eq f.

  Instance Morphism_eq
    (A : Type)
    {Eq_A : Eq A}
    {PartialSetoid_A : PartialSetoid A} :
    Morphism (@eq A Eq_A).
  Proof.
    intros x x' x_eq_x' y y' y_eq_y'; split.
      intros x_eq_y; now transitivity x; [symmetry| transitivity y].
    intros x'_eq_y'; now transitivity x'; [| transitivity y'; symmetry].
  Qed.
End Setoid.
Import Setoid.

Module Label.
  Class Signature
    (L : Type)
    {Eq_L : Eq L} :
    Type :=
    {
      Ok :
        list L ->
        Prop;
      Morphism_Ok :>
        Morphism Ok;
    }.
  Arguments Ok {L} {Eq_L} _.

  Class Theory
    {L : Type}
    {Eq_L : Eq L}
    (Signature_L : Signature L) :
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
  Class Signature
    (L : Type)
    {Eq_L : Eq L}

    (S : Type)
    {Eq_S : Eq S} :
    Type :=
    {
      Initial :
        S ->
        Prop;
      Morphism_Initial :>
        Morphism Initial;
      Transition :
        S ->
        L ->
        S ->
        Prop;
      Morphism_Transition :>
        Morphism Transition;
      Ok :
        list L ->
        S ->
        Prop;
      Morphism_Ok :>
        Morphism Ok;
    }.
  Arguments Initial {L} {Eq_L} {S} {Eq_S} _.
  Arguments Transition {L} {Eq_L} {S} {Eq_S} _.
  Arguments Ok {L} {Eq_L} {S} {Eq_S} _.

  Class Theory
    {L : Type}
    {Eq_L : Eq L}
    (Signature_L : Label.Signature L)

    {S : Type}
    {Eq_S : Eq S}
    (Signature_S : Signature L S) :
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

  Class WeaklyReflectiveHomomorphism
    {L : Type}
    {Eq_L : Eq L}

    {S : Type}
    {Eq_S : Eq S}
    (Signature_S : Signature L S)

    {S' : Type}
    {Eq_S' : Eq S'}
    (Signature_S' : Signature L S')

    (h : S -> S') :
    Prop :=
    {
      Setoid_Morphism :>
        Morphism h;
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
        eq (h s) (h s') /\
        Signature_S.(Initial) s';
      Weakly_Ok :
        forall
        (x : list L)
        (s : S),
        Signature_S'.(Ok) x (h s) ->
        exists
        s' : S,
        eq (h s) (h s') /\
        Signature_S.(Ok) x s';
    }.

  Program Definition Signature_Image
    {L : Type}
    {Eq_L : Eq L}

    {S : Type}
    {Eq_S : Eq S}

    {S' : Type}
    {Eq_S' : Eq S'}
    (Signature_S' : Signature L S')

    (h : S -> S')
    {Morphism_h : Morphism h} :
    Signature L S :=
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

  Instance Theory_Image
    {L : Type}
    {Eq_L : Eq L}
    {Reflexive_L : Reflexive (@eq L Eq_L)}
    (Signature_L : Label.Signature L)

    {S : Type}
    {Eq_S : Eq S}
    {Setoid_S : Setoid S}
    (Signature_S : Signature L S)
    {Theory_S : Theory Signature_L Signature_S}

    {S' : Type}
    {Eq_S' : Eq S'}
    (Signature_S' : Signature L S')

    (h : S -> S')
    {Homomorphism_h : WeaklyReflectiveHomomorphism Signature_S Signature_S' h} :
    Theory Signature_L (Signature_Image Signature_S' h).
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

Module Algebraic.
  Class Signature
    (L : Type)
    {Eq_L : Eq L}

    (S : Type)
    {Eq_S : Eq S} :
    Type :=
    {
      init :
        S;
      f :
        S ->
        L ->
        option S;
      Morphism_f :>
        Morphism f;
      Ok :
        list L ->
        S ->
        Prop;
      Morphism_Ok :>
        Morphism Ok;
    }.
  Arguments init {L} {Eq_L} {S} {Eq_S} _.
  Arguments f {L} {Eq_L} {S} {Eq_S} _.
  Arguments Ok {L} {Eq_L} {S} {Eq_S} _.

  Class Theory
    {L : Type}
    {Eq_L : Eq L}
    (Signature_L : Label.Signature L)

    {S : Type}
    {Eq_S : Eq S}
    (Signature_S : Signature L S) :
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
        eq (Signature_S.(f) s u₀) (Some t) /\
        Signature_S.(Ok) (u₀ :: x₀) t;
    }.

  Program Definition to_Relational_Signature
    {L : Type}
    {Eq_L : Eq L}

    {S : Type}
    {Eq_S : Eq S}
    {Setoid_S : Setoid S}
    (Signature_S : Signature L S) :
    Relational.Signature L S :=
    {|
      Relational.Initial x :=
        eq x Signature_S.(init);
      Relational.Transition s u t :=
        eq (Signature_S.(f) s u) (Some t);
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

  Instance to_Relational_Theory
    {L : Type}
    {Eq_L : Eq L}
    (Signature_L : Label.Signature L)

    {S : Type}
    {Eq_S : Eq S}
    {Setoid_S : Setoid S}
    (Signature_S : Signature L S)
    {Theory_S : Theory Signature_L Signature_S} :
    Relational.Theory Signature_L (to_Relational_Signature Signature_S).
  Proof.
    split.
      intros s s_eq_init.
      apply Morphism_Ok with [] (Signature_S.(init)).
          constructor.
        assumption.
      apply Ok_init.
    intros u₀ x₀ s Ok_x Ok_x₀_s.
    now apply executable.
  Qed.

  Class WeaklyReflectiveHomomorphism
    {L : Type}
    {Eq_L : Eq L}

    {S : Type}
    {Eq_S : Eq S}
    (Signature_S : Signature L S)

    {S' : Type}
    {Eq_S' : Eq S'}
    (Signature_S' : Signature L S')

    (h : S -> S') :
    Prop :=
    {
      Setoid_Morphism :>
        Morphism h;
      Preserves_init :
        eq (Signature_S'.(init)) (h Signature_S.(init));
      Preserves_f :
        forall
        (s : S)
        (u : L),
        eq (Signature_S'.(f) (h s) u) (option_map h (Signature_S.(f) s u));
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
        eq (h s) (h s') /\
        Signature_S.(Ok) x s';
    }.

  Definition to_Relational_WeaklyReflectiveHomomorphism
    {L : Type}
    {Eq_L : Eq L}

    {S : Type}
    {Eq_S : Eq S}
    {Setoid_S : Setoid S}
    (Signature_S : Signature L S)

    {S' : Type}
    {Eq_S' : Eq S'}
    {Setoid_S' : Setoid S'}
    (Signature_S' : Signature L S')

    (h : S -> S')
    {Homomorphism_h : WeaklyReflectiveHomomorphism Signature_S Signature_S' h} :
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

  Program Definition Signature_Image
    {L : Type}
    {Eq_L : Eq L}

    {S : Type}
    {Eq_S : Eq S}
    (Signature_S : Signature L S)

    {S' : Type}
    {Eq_S' : Eq S'}
    (Signature_S' : Signature L S')

    (h : S -> S')
    {Morphism_h : Morphism h} :
    Signature L S :=
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

  Instance Theory_Image
    {L : Type}
    {Eq_L : Eq L}
    {Setoid_L : Setoid L}
    (Signature_L : Label.Signature L)

    {S : Type}
    {Eq_S : Eq S}
    {Setoid_S : Setoid S}
    (Signature_S : Signature L S)
    {Theory_S : Theory Signature_L Signature_S}

    {S' : Type}
    {Eq_S' : Eq S'}
    {Setoid_S' : Setoid S'}
    (Signature_S' : Signature L S')

    (h : S -> S')
    {Homomorphism_h : WeaklyReflectiveHomomorphism Signature_S Signature_S' h} :
    Theory Signature_L (Signature_Image Signature_S Signature_S' h).
  Proof.
    split; simpl.
      apply Preserves_Ok, Ok_init.
    intros u₀ x₀ s Ok_x Ok'_x₀_h_s.
    apply Weakly_Ok in Ok'_x₀_h_s as (s' & h_s_eq_h_s' & Ok_x₀_s').
    specialize (executable u₀ x₀ s' Ok_x Ok_x₀_s') as
      (t' & f_s'_u₀_eq_t' & Ok_x_t').
    assert (H : eq (option_map h (Signature_S.(f) s u₀)) (option_map h (Some t'))).
      now rewrite <- Preserves_f, h_s_eq_h_s', Preserves_f, f_s'_u₀_eq_t'.
    destruct (Signature_S.(f) s u₀) as [t|]; inversion_clear H.
    exists t; split; [reflexivity|].
    now apply Morphism_Ok with (u₀ :: x₀) (h t'); [..| apply Preserves_Ok].
  Qed.
End Algebraic.

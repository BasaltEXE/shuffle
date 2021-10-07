Require Import
  Coq.Relations.Relation_Definitions
  Coq.Relations.Relation_Operators
  Coq.Relations.Operators_Properties.

Require Import
  Coq.Program.Basics
  Coq.Classes.RelationClasses
  Coq.Classes.Morphisms.

Require Import
  Setoid.

#[global]
Add Parametric Relation : Prop impl
  reflexivity proved by impl_Reflexive
  transitivity proved by impl_Transitive
  as PreOrder_impl.

Section Classes.
  Context
    {A : Type}
    (R : relation A).

  Class Connex :
    Prop :=
    connexity :
    forall
    x y : A,
    R x y \/
    R y x.

  Class Functional :
    Prop :=
    functionality :
    forall
    x y y' : A,
    R x y ->
    R x y' ->
    y = y'.

  #[global]
  Instance Asymmetric_Irreflexive (Asymmetric_R : Asymmetric R) : Irreflexive R.
  Proof.
    intros x R_x_x.
    now apply asymmetry with x x.
  Qed.
End Classes.

Module Restriction.
  Section Restriction.
    Context
      {A : Type}
      (P : A -> Prop)
      (R : relation A).

    Definition Restriction :
      relation (sig P) :=
      fun x y => R (proj1_sig x) (proj1_sig y).

    Let R' :
      relation (sig P) :=
      Restriction.

    #[global]
    Instance reflexive {Reflexive_R : Reflexive R} :
      Reflexive R'.
    Proof.
      intros (x & P_x).
      apply Reflexive_R.
    Qed.

    #[global]
    Instance irreflexive {Irreflexive_R : Irreflexive R} :
      Irreflexive R'.
    Proof.
      intros (x & P_x).
      apply Irreflexive_R.
    Qed.

    #[global]
    Instance symmetric {Symmetric_R : Symmetric R} :
      Symmetric R'.
    Proof.
      intros (x & P_x) (y & P_y).
      apply Symmetric_R.
    Qed.

    #[global]
    Instance asymmetric {Asymmetric_R : Asymmetric R} :
      Asymmetric R'.
    Proof.
      intros (x & P_x) (y & P_y).
      apply Asymmetric_R.
    Qed.

    #[global]
    Instance transitive {Transitive_R : Transitive R} :
      Transitive R'.
    Proof.
      intros (x & P_x) (y & P_y) (z & P_z).
      apply Transitive_R.
    Qed.

    #[global]
    Instance preorder {PreOrder_R : PreOrder R} :
      PreOrder R'.
    Proof.
      constructor; eauto with typeclass_instances.
    Qed.

    #[global]
    Instance equivalence {Equivalence_R : Equivalence R} :
      Equivalence R'.
    Proof.
      constructor; eauto with typeclass_instances.
    Qed.
  End Restriction.

  Section PartialOrder.
    Context
      {A : Type}
      (P : A -> Prop)
      (R Eq : relation A).

    Let R' :
      relation (sig P) :=
      Restriction P R.

    Let Eq' :
      relation (sig P) :=
      Restriction P Eq.

    #[global]
    Instance antisymmetric `{Antisymmetric_R : Antisymmetric A R Eq} :
      Antisymmetric (sig P) R' Eq'.
    Proof.
      intros (x & P_x) (y & P_y).
      apply Antisymmetric_R.
    Qed.

    #[global]
    Instance partial_order `{PartialOrder_R : PartialOrder A R Eq} :
      PartialOrder R' Eq'.
    Proof.
      intros (x & P_x) (y & P_y).
      apply PartialOrder_R.
    Qed.
  End PartialOrder.
End Restriction.
Import Restriction(Restriction).

Module ReflexiveTransitive.
  Section ReflexiveTransitive.
    Context
      {A : Type}
      (R : relation A).

    Definition Closure :
      relation A :=
      clos_refl_trans_1n _ R.

    #[global]
    Instance subrelation :
      subrelation R Closure.
    Proof.
      intros x y R_x_y.
      now apply clos_rt1n_step.
    Qed.

    #[global]
    Instance reflexive :
      Reflexive Closure.
    Proof.
      intros x.
      apply rt1n_refl.
    Qed.

    #[global]
    Instance transitive :
      Transitive Closure.
    Proof.
      intros x y z; unfold Closure.
      rewrite <- 3!clos_rt_rt1n_iff.
      now constructor 3 with y.
    Qed.

    #[global]
    Add Parametric Relation : A Closure
      reflexivity proved by reflexive
      transitivity proved by transitive
      as preorder.

    Add Parametric Morphism
      {B : Type}
      (S : relation B)
      (f : A -> B)
      `{PreOrder_R : PreOrder B S}
      `{Proper_f : Proper (A -> B) (R ++> S)%signature f} : f with signature
      Closure ++> S as morphism.
    Proof.
      intros x y Closure_x_y.
      induction Closure_x_y as
        [x|
      x x' y R_x_x' Closure_x'_y IHx'_y].
        reflexivity.
      now transitivity (f x'); [rewrite R_x_x'|].
    Qed.
  End ReflexiveTransitive.

  Section Restriction.
    Variables
      (A : Type)
      (P : A -> Prop)
      (R : relation A)
      (Proper_P : Proper (R ++> impl) P)
      (x y : A)
      (P_x : P x).

    Lemma Restriction :
      Closure R x y ->
      exists
      P_y : P y,
      Closure
        (Restriction P R)
        (exist P x P_x)
        (exist P y P_y).
    Proof.
      induction 1 as
        [x|
      x x' y R_x_x' Closure_x'_y IHx'_y].
        now exists P_x.
      assert (P_x' : P x') by now rewrite <- R_x_x'.
      specialize IHx'_y with P_x' as (P_y & H).
      now exists P_y; constructor 2 with (exist P x' P_x').
    Qed.
  End Restriction.
End ReflexiveTransitive.

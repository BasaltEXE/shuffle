Set Implicit Arguments.

Require Import Coq.Arith.Arith.

Require Import Coq.Lists.SetoidList.
Import ListNotations.

Require Import
  Shuffle.Misc
  Shuffle.Relations.

Lemma Forall_cons_iff : forall
  (A : Type)
  (P : A -> Prop)
  (u₀ : A)
  (x₀ : list A),
  Forall P (u₀ :: x₀) <->
    P u₀ /\
    Forall P x₀.
Proof.
  split.
    intros Forall_x.
    constructor.
      now apply Forall_inv with x₀.
    now apply Forall_inv_tail with u₀.
  intros [P_u₀ Forall_x₀].
  now constructor.
Qed.

Lemma not_In_Forall : forall
  (A : Type)
  (u : A)
  (y : list A),
  ~ List.In u y <->
  Forall (fun v => u <> v) y.
Proof.
  induction y as [| v₀ y₀ IHy₀].
    easy.
  rewrite Forall_cons_iff, not_in_cons; firstorder.
Qed.

Section InA.
  Variables
    (A : Type)
    (eqA : A -> A -> Prop)
    (u v₀ : A)
    (y₀ y : list A).

  Lemma not_InA_cons :
    ~ InA eqA u (v₀ :: y₀) <->
      ~ eqA u v₀ /\
      ~ InA eqA u y₀.
  Proof.
    rewrite InA_cons; firstorder.
  Qed.

  Lemma not_InA_iff :
    ~ InA eqA u y <->
    Forall (fun v => ~ eqA u v) y.
  Proof.
    now rewrite InA_altdef, <- Forall_Exists_neg.
  Qed.
End InA.

Module Tail.
  Section Tail.
    Variables
      (A : Type).

    Inductive Tail : list A -> list A -> Prop :=
    | intro :
      forall
        (u : A)
        (x : list A),
        Tail (u :: x) x.

    #[global]
    Instance asymmetric :
      Asymmetric Tail.
    Proof.
      intros x y Tail_x_y Tail_y_x.
      induction Tail_x_y as (u₀ & x₀).
      inversion Tail_y_x as (u₁).
      now enough ([] = [u₀; u₁]);
        [| apply app_inv_tail with x].
    Qed.

    #[global]
    Instance functional :
      Functional Tail.
    Proof.
      intros x y y' Tail_x_y Tail_x_y'.
      induction Tail_x_y as (u₀ & x₀).
      now inversion_clear Tail_x_y' as (u₁).
    Qed.

    #[global]
    Instance irreflexive :
      Irreflexive Tail.
    Proof.
      intros x Tail_x_x.
      now apply asymmetric with (1 := Tail_x_x).
    Qed.

    Variables
      (v₀ : A)
      (y₀ y x : list A).

    Lemma inv :
      Tail y y₀ ->
      exists
        v₀ : A,
        y = v₀ :: y₀.
    Proof.
      inversion_clear 1.
      now exists u.
    Qed.

    Lemma iff :
      Tail y y₀ <->
      (exists
        v₀ : A,
        y = v₀ :: y₀).
    Proof.
      now clear v₀; split;
        [apply inv| intros (v₀' & ->)].
    Qed.

    Lemma nil_inv :
      ~ Tail [] x.
    Proof.
      easy.
    Qed.

    Lemma nil_iff :
      Tail [] x <->
      False.
    Proof.
      now split.
    Qed.

    Lemma cons_inv :
      Tail (v₀ :: y₀) x ->
      y₀ = x.
    Proof.
      now inversion_clear 1.
    Qed.

    Lemma cons_iff :
      Tail (v₀ :: y₀) x <->
      y₀ = x.
    Proof.
      now split;
        [apply cons_inv| intros <-].
    Qed.
  End Tail.

  Add Parametric Relation (A : Type) : (list A) (Tail (A := A))
    as Tail_rel.
End Tail.
Export Tail(Tail).

Module Skip.
  Section Skip.
    Variables
      (A : Type).

    Definition Skip :
      relation (list A) :=
      ReflexiveTransitive.Closure (@Tail A).

    Section Properties.
      Variables
        (v₀ : A)
        (y₀ x : list A).

      Lemma nil_inv :
        Skip [] x ->
        x = [].
      Proof.
        destruct 1 as [| y z Tail_x_y _]; [reflexivity|].
        contradict Tail_x_y; apply Tail.nil_inv.
      Qed.

      Lemma nil_iff :
        Skip [] x <->
        x = [].
      Proof.
        split;
          [apply nil_inv| intros ->; constructor].
      Qed.

      Lemma cons_inv :
        Skip (v₀ :: y₀) x ->
          x = v₀ :: y₀ \/
          Skip y₀ x.
      Proof.
        now inversion_clear 1;
          [left| right];
          [| apply Tail.cons_inv in H0 as ->].
      Qed.

      Lemma cons_iff :
        Skip (v₀ :: y₀) x <->
          x = v₀ :: y₀ \/
          Skip y₀ x.
      Proof.
        split.
          apply cons_inv.
        now intros [->| Skip_y₀_x];
          [constructor| constructor 2 with y₀].
      Qed.

      Variables
        z : list A.

      Lemma inv :
        Skip x z ->
        (exists
          y : list A,
          x = y ++ z).
      Proof.
        clear y₀; induction 1 as [| x x₀ z Tail_x_x₀ Skip_x₀_z (y₀ & IHx₀_z)].
          now exists [].
        destruct Tail_x_x₀ as (u₀ & x₀).
        now exists (u₀ :: y₀); rewrite IHx₀_z.
      Qed.

      Lemma iff :
        Skip x z <->
        (exists
          y : list A,
          x = y ++ z).
      Proof.
        clear v₀ y₀; split.
          apply inv.
        intros [y H].
        revert dependent x.
        induction y as [| v₀ y₀ IHy₀].
          now intros ? ->.
        intros [| u₀ x₀] [= _ ->].
        constructor 2 with (y₀ ++ z).
          constructor.
        now apply IHy₀.
      Qed.
    End Properties.

    #[global]
    Instance antisymmetric :
      Antisymmetric (list A) eq Skip.
    Proof.
      intros x y Skip_x_y Skip_y_x.
      apply iff in
        Skip_x_y as (y' & H),
        Skip_y_x as (x' & G).
      enough (x' = [] /\ y' = []) as (-> & ->) by easy.
      enough (x' ++ y' = []) by
        now apply app_eq_nil.
      enough ([] ++ y = (x' ++ y') ++ y) by
        now symmetry; apply app_inv_tail with y.
      now rewrite <- app_assoc, <- H.
    Qed.

    #[global]
    Instance partial_order :
      PartialOrder eq Skip.
    Proof.
      intros x y.
      split.
        now intros ->.
      intros (Skip_x_y & Skip_y_x).
      now apply antisymmetric.
    Qed.

    Lemma not_flip_Tail :
      forall
      x y : list A,
      Skip x y ->
      ~ Tail y x.
    Proof.
      intros x y Skip_x_y.
      assert (not_Tail_x_x : ~ Tail x x) by apply irreflexivity.
      contradict not_Tail_x_x.
      enough (x_eq_y : x = y).
        now rewrite x_eq_y at 1.
      apply antisymmetry with (1 := Skip_x_y).
      now rewrite not_Tail_x_x.
    Qed.
  End Skip.

  Notation Forall P y :=
    (forall
      x,
      Skip y x ->
      P x).

  Module Forall.
    Section Forall.
      Variables
        (A : Type)
        (P : list A -> Prop)
        (v₀ : A)
        (y₀ : list A).

      Lemma nil :
        P [] ->
        Forall P [].
      Proof.
        intros P_y x Skip_y_x.
        now apply nil_inv in Skip_y_x as ->.
      Qed.

      Lemma cons :
        P (v₀ :: y₀) ->
        Forall P y₀ ->
        Forall P (v₀ :: y₀).
      Proof.
        intros P_y P_y₀ x Skip_y_x.
        now apply cons_inv in Skip_y_x as [->| Skip_y₀_x];
          [| apply P_y₀].
      Qed.
    End Forall.
  End Forall.

  Notation Exists P y :=
    (exists
      x,
        Skip y x /\
        P x).

  Module Exists.
    Section Exists.
      Variables
        (A : Type)
        (P : list A -> Prop)
        (v₀ : A)
        (y₀ y : list A).

      Lemma refl :
        P y ->
        Exists P y.
      Proof.
        intros P_y.
        now exists y.
      Qed.

      Lemma cons :
        Exists P y₀ ->
        Exists P (v₀ :: y₀).
      Proof.
        intros (x & Skip_y₀_x & P_x).
        now exists x; split;
          [constructor 2 with y₀|].
      Qed.
    End Exists.
  End Exists.
End Skip.
Export Skip(Skip).

Module Nth.
  Notation Nth x n v :=
    (nth_error x n = Some v).

  Section Properties.
    Variables
      (A : Type)
      (u₀ : A)
      (x₀ : list A)
      (n : nat)
      (v : A).

    Lemma nil_inv :
      ~ Nth [] n v.
    Proof.
      intros n_to_v.
      now destruct n.
    Qed.

    Lemma nil_iff :
      Nth [] n v <-> False.
    Proof.
      now split; [apply nil_inv|].
    Qed.

    Lemma cons_O :
      u₀ = v -> Nth (u₀ :: x₀) O v.
    Proof.
      intros u₀_eq_v.
      now simpl; f_equal.
    Qed.

    Lemma cons_O_inv :
      Nth (u₀ :: x₀) O v -> u₀ = v.
    Proof.
      intros n_to_v.
      now inversion_clear n_to_v.
    Qed.

    Lemma cons_O_iff :
      Nth (u₀ :: x₀) O v <-> u₀ = v.
    Proof.
      split;
        [apply cons_O_inv| apply cons_O].
    Qed.

    Lemma cons_S :
      Nth x₀ n v -> Nth (u₀ :: x₀) (S n) v.
    Proof.
      easy.
    Qed.

    Lemma cons_S_inv :
      Nth (u₀ :: x₀) (S n) v -> Nth x₀ n v.
    Proof.
      easy.
    Qed.

    Lemma cons_S_iff :
      Nth (u₀ :: x₀) (S n) v <-> Nth x₀ n v.
    Proof.
      split;
        [apply cons_S| apply cons_S_inv].
    Qed.
  End Properties.
End Nth.
Export Nth(Nth).

Module NthError.
  Section Properties.
    Variables
      (A : Type)
      (x : list A)
      (n : nat)
      (v : A).

    Lemma None_iff :
      nth_error x n = None <->
      n >= length x.
    Proof.
      apply nth_error_None.
    Qed.

    Lemma None_ge :
      nth_error x n = None ->
      n >= length x.
    Proof.
      apply None_iff.
    Qed.

    Lemma ge_None :
      n >= length x ->
      nth_error x n = None.
    Proof.
      apply None_iff.
    Qed.

    Lemma Some_iff :
      (exists v : A, Nth x n v) <-> n < length x.
    Proof.
      clear v; split.
        intros [v n_to_v].
        now apply nth_error_Some; rewrite n_to_v.
      now destruct (nth_error x n) as [v|] eqn: nth;
        [exists v| apply None_ge, Lt.le_not_lt in nth].
    Qed.

    Lemma Some_lt :
      Nth x n v ->
      n < length x.
    Proof.
      intros n_to_v.
      now apply Some_iff; exists v.
    Qed.

    Lemma lt_Some :
      n < length x ->
      exists v : A, Nth x n v.
    Proof.
      apply Some_iff.
    Qed.
  End Properties.

  Section Misc.
    Variables
      (A : Type)
      (x y : list A)
      (n : nat).

    Lemma spec :
      OptionSpec
        (fun _ => n < length x)
        (n >= length x)
        (nth_error x n).
    Proof.
      now destruct (nth_error x n) as [v|] eqn: nth; constructor;
        [apply Some_lt with v| apply None_ge].
    Qed.

    Lemma pointwise_eq :
        (forall n : nat, nth_error x n = nth_error y n) ->
        x = y.
    Proof.
      revert y.
      induction x as [| u₀ x₀]; intros [| v₀ y₀] x_eq_y.
            reflexivity.
          discriminate (x_eq_y 0).
        discriminate (x_eq_y 0).
      f_equal.
        now specialize x_eq_y with 0 as [=].
      now specialize IHx₀ with (1 := fun n => x_eq_y (S n)).
    Qed.
  End Misc.
End NthError.

Module Replace.
  Fixpoint replace
    (A : Type)
    (x : list A)
    (n : nat)
    (v : A)
    {struct x} :
    option (list A) :=
      match x, n with
      | u₀ :: x₀, O => Some (v :: x₀)
      | u₀ :: x₀, S n' => bind (replace x₀ n' v)
        (fun x₀' => Some (u₀ :: x₀'))
      | _, _ => None
      end.

  Notation Replace
    x
    n
    v
    y :=
    (replace x n v = Some y).

  Definition Ok
    (A : Type)
    (x : list A)
    (n : nat)
    (v : A)
    (y : list A) :
    Prop :=
      n < length x /\
      length x = length y /\
      Nth y n v /\
      (forall m : nat,
        m <> n ->
        nth_error x m = nth_error y m).

  Section Properties.
    Variables
      (A : Type)
      (x : list A)
      (n : nat)
      (v : A)
      (y : list A).

    Lemma None_iff :
      replace x n v = None <-> n >= length x.
    Proof.
      clear y; revert x n.
      induction x as [| u₀ x₀ IHx₀]; intros n.
        now split; [auto with arith|].
      destruct n as [| n'].
        split; [discriminate 1|].
        intros n_ge_x.
        now apply PeanoNat.Nat.nle_succ_0 in n_ge_x.
      simpl; split.
        specialize IHx₀ with n'.
        destruct (replace x₀ n' v) as [y|]; simpl.
          discriminate 1.
        now intros _; apply le_n_S, IHx₀.
      intros n_ge_x.
      enough (replace x₀ n' v = None) as -> by reflexivity.
      now apply IHx₀, le_S_n.
    Qed.

    Lemma None_ge :
      replace x n v = None -> n >= length x.
    Proof.
      apply None_iff.
    Qed.

    Lemma ge_None :
      n >= length x -> replace x n v = None.
    Proof.
      apply None_iff.
    Qed.

    Lemma Some_iff :
      Replace x n v y <->
      Ok x n v y.
    Proof with (auto with arith).
      unfold Ok; revert x n y.
      induction x as [| u₀ x₀ IHx₀]; intros n y.
        split; [discriminate 1|].
        intros (n_lt_x & n_to_v & H).
        contradict n_lt_x; apply PeanoNat.Nat.nlt_0_r.
      destruct n as [| n']; simpl.
        split.
          now intros [= <-]; (repeat split);
            [auto with arith|..| destruct m as [| m']].
        destruct y as [| v₀ y₀]; intros (n_lt_x & x_eq_y & [= ->] & H).
        repeat f_equal; apply NthError.pointwise_eq.
        intro m; refine (H (S m) _)...
      destruct y as [| v₀ y₀].
        split.
          destruct (replace x₀ n' v); intros [=].
        intros (_ & _ & [=] & _).
      specialize IHx₀ with n' y₀.
      rewrite <- Nat.succ_lt_mono.
      destruct (replace x₀ n' v) as [y₀'|]; simpl.
        split.
          intros [= -> ->];
          now (repeat split);
            [| f_equal| |intros [| m']; [reflexivity| rewrite Nat.succ_inj_wd_neg]]; apply IHx₀.
        intros (n_lt_x & [= x_eq_y] & n_to_v & H).
        enough (H' : Some u₀ = Some v₀ /\ Some y₀' = Some y₀) by
          now destruct H' as ([= ->] & [= ->]).
        split.
          apply (H 0)...
        now apply IHx₀; (repeat split);
          [..| intros m' m'_neq_n'; apply (H (S m')), not_eq_S].
      split; [intros [=]|].
      intros (n_lt_x & [= x_eq_y] & n_to_v & H).
      enough (H' : None = Some y₀) by inversion H'.
      apply IHx₀; (repeat split); [assumption..|].
      now intros m' m'_neq_n'; apply (H (S m')), not_eq_S.
    Qed.

    Lemma Some_lt :
      Replace x n v y ->
        Ok x n v y.
    Proof.
      apply Some_iff.
    Qed.
  End Properties.

  Section Misc.
    Variables
      (A : Type)
      (x : list A)
      (n : nat)
      (v : A).

    Definition spec :
      OptionSpec
        (Ok x n v)
        (n >= length x)
        (replace x n v).
    Proof.
      now destruct (replace x n v) as [y|] eqn: H; constructor;
        [apply Some_iff| apply None_iff with v].
    Qed.

    Lemma lt_Some :
      n < length x ->
      exists y : list A,
        Replace x n v y /\
        Ok x n v y.
    Proof.
      intros n_lt_x.
      now destruct spec as [y (_ & x_eq_y & n_to_v & H)| n_ge_x];
        [exists y| apply lt_not_le in n_lt_x].
    Qed.
  End Misc.
End Replace.
Export Replace(replace).

Module ForNth.
  Definition ForNth
    (A : Type)
    (P : nat -> A -> Prop)
    (x : list A) :
    Prop :=
      forall (n : nat) (u : A), Nth x n u -> P n u.

  Section Properties.
    Variables
      (A : Type)
      (P : nat -> A -> Prop)
      (u₀ : A)
      (x₀ : list A).

    Lemma nil :
      ForNth P [].
    Proof.
      intros n v n_to_v.
      now apply Nth.nil_inv in n_to_v.
    Qed.

    Lemma nil_iff :
      ForNth P [] <-> True.
    Proof.
      now split; [| intros _; apply nil].
    Qed.

    Lemma cons :
      P O u₀ ->
      ForNth (fun n => P (S n)) x₀ ->
      ForNth P (u₀ :: x₀).
    Proof.
      intros P_u₀ P_x₀.
      intros [| n'] v n_to_v.
        now apply Nth.cons_O_inv in n_to_v as ->.
      apply Nth.cons_S_inv in n_to_v as n'_to_v.
      now apply P_x₀.
    Qed.

    Lemma cons_inv :
      ForNth P (u₀ :: x₀) ->
      (P O u₀ /\ ForNth (fun n => P (S n)) x₀).
    Proof.
      intros P_x.
      now split;
        [| intros n v n_to_v]; apply P_x.
    Qed.

    Lemma cons_iff :
      ForNth P (u₀ :: x₀) <->
      (P O u₀ /\ ForNth (fun n => P (S n)) x₀).
    Proof.
      split.
        apply cons_inv.
      now intros (P_u₀ & P_x₀); apply cons.
    Qed.
  End Properties.
End ForNth.
Export ForNth(ForNth).

Module ForNth2.
  Definition ForNth2
    (A B : Type)
    (P : nat -> A -> B -> Prop)
    (x : list A)
    (y : list B) :
    Prop :=
      forall
      (n : nat)
      (u : A)
      (v : B),
      Nth x n u ->
      Nth y n v ->
      P n u v.

  Section Properties.
    Variables
      (A B : Type)
      (P : nat -> A -> B -> Prop)
      (u₀ : A)
      (x₀ x : list A)
      (v₀ : B)
      (y₀ y : list B).

    Lemma nil_r :
      ForNth2 P [] y.
    Proof.
      intros n u v.
      now rewrite ?Nth.nil_iff.
    Qed.

    Lemma nil_r_iff :
      ForNth2 P [] y <-> True.
    Proof.
      now split;
        [| intros _; apply nil_r].
    Qed.

    Lemma nil_l :
      ForNth2 P x [].
    Proof.
      intros n u v.
      now rewrite ?Nth.nil_iff.
    Qed.

    Lemma nil_l_iff :
      ForNth2 P x [] <-> True.
    Proof.
      now split;
        [| intros _; apply nil_l].
    Qed.

    Lemma cons :
      P O u₀ v₀ ->
      ForNth2 (fun n => P (S n)) x₀ y₀ ->
      ForNth2 P (u₀ :: x₀) (v₀ :: y₀).
    Proof.
      intros P_u₀_v₀ P_x₀_y₀ [| n'] u v n_to_u n_to_v.
        now apply Nth.cons_O_inv in n_to_u as ->, n_to_v as ->.
      now apply Nth.cons_S_inv in n_to_u, n_to_v; apply P_x₀_y₀.
    Qed.

    Lemma cons_inv :
      ForNth2 P (u₀ :: x₀) (v₀ :: y₀) ->
      P O u₀ v₀ /\ ForNth2 (fun n => P (S n)) x₀ y₀.
    Proof.
      intros P_x_y.
      now split;
        [| intros n u v n_to_u n_to_v];
        apply P_x_y.
    Qed.

    Lemma cons_iff :
      ForNth2 P (u₀ :: x₀) (v₀ :: y₀) <->
      (P O u₀ v₀ /\ ForNth2 (fun n => P (S n)) x₀ y₀).
    Proof.
      now split;
        [apply cons_inv| intros (P_u₀_v₀ & P_x₀_y₀); apply cons].
    Qed.
  End Properties.

  Section Flip.
      Variables
      (A B : Type)
      (P : nat -> A -> B -> Prop)
      (x : list A)
      (y : list B)
      (u : A)
      (v : B)
      (n : nat).

    Lemma flip :
      ForNth2 P x y -> ForNth2 (fun n x y => P n y x) y x.
    Proof.
      revert y P.
      induction x as [| u₀ x₀ IHx₀]; intros y P P_x_y.
        apply nil_l.
      destruct y as [| v₀ y₀].
        apply nil_r.
      apply cons_inv in P_x_y as (P_u₀_v₀ & P_x₀_y₀).
      now apply cons, IHx₀.
    Qed.

    Lemma from_left :
      length x = length y ->
      ForNth2 P x y ->
      Nth x n u ->
      exists v : B,
        Nth y n v /\
        P n u v.
    Proof.
      clear v; intros length_eq P_x_y n_to_u.
      destruct (nth_error y n) as [v|] eqn: nth.
        now exists v; split; [| apply P_x_y].
      apply nth_error_None in nth as n_ge_y.
      contradict n_ge_y; apply lt_not_le.
      now rewrite <- length_eq; apply NthError.Some_lt with u.
    Qed.
  End Flip.

  Lemma from_right : forall
    (A B : Type)
    (P : nat -> A -> B -> Prop)
    (x : list A)
    (y : list B)
    (v : B)
    (n : nat),
    length x = length y ->
    ForNth2 P x y ->
    Nth y n v ->
    exists u : A,
      Nth x n u /\
      P n u v.
  Proof.
    intros A B P x y v n length_eq P_x_y n_to_v.
    apply from_left with (x := y) (P := fun n x y => P n y x ); try easy.
      now apply flip.
  Qed.
End ForNth2.
Export ForNth2(ForNth2).

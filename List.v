Set Implicit Arguments.

Require Import
  Coq.Arith.Arith
  Coq.Structures.Equalities
  Coq.Lists.SetoidList
  Lia.

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
      (x y : list A)
      (n : nat)
      (v : A).

    Lemma ge_iff :
      n >= length x <->
      nth_error x n = None.
    Proof.
      symmetry; apply nth_error_None.
    Qed.

    Lemma None_ge :
      nth_error x n = None ->
      n >= length x.
    Proof.
      apply ge_iff.
    Qed.

    Lemma ge_None :
      n >= length x ->
      nth_error x n = None.
    Proof.
      apply ge_iff.
    Qed.

    Lemma lt_iff :
      n < length x <->
      (exists v : A, nth_error x n = Some v).
    Proof.
      clear v; split.
        intros n_lt_x%nth_error_Some.
        now destruct (nth_error x n) as [v|]; [exists v|].
      intros [v n_to_v].
      now apply nth_error_Some; rewrite n_to_v.
    Qed.

    Lemma Some_lt :
      Nth x n v ->
      n < length x.
    Proof.
      intros n_to_v.
      now apply lt_iff; exists v.
    Qed.

    Lemma lt_Some :
      n < length x ->
      exists v : A, Nth x n v.
    Proof.
      apply lt_iff.
    Qed.

    Lemma In_iff :
      (exists n : nat, nth_error x n = Some v) <->
      In v x.
    Proof.
      clear n; split.
        intros (n & n_to_v); now apply nth_error_In with n.
      apply In_nth_error.
    Qed.

    Lemma middle :
      forall
      x y : list A,
      nth_error (x ++ v :: y) (length x) = Some v.
    Proof.
      clear x y; intros x y.
      transitivity (Some (nth (length x) (x ++ v :: y) v)).
        apply nth_error_nth'; rewrite app_length; simpl; lia.
      f_equal; apply nth_middle.
    Qed.

    Lemma split_iff :
      (exists
      y z : list A,
      x = y ++ v :: z /\
      length y = n) <->
      nth_error x n = Some v.
    Proof.
      clear y; split.
        intros (y & z & -> & <-); apply middle.
      apply nth_error_split.
    Qed.

    Lemma eq_iff :
      x = y <->
      (forall
      n : nat,
      nth_error x n = nth_error y n).
    Proof.
      split; [now intros ->|].
      revert y.
      induction x as [| u₀ x₀]; intros [| v₀ y₀] x_eq_y.
            reflexivity.
          discriminate (x_eq_y 0).
        discriminate (x_eq_y 0).
      f_equal.
        now specialize x_eq_y with 0 as [=].
      now specialize IHx₀ with (1 := fun n => x_eq_y (S n)).
    Qed.

    Lemma app_lt :
      n < length x ->
      nth_error (x ++ y) n = nth_error x n.
    Proof.
      apply nth_error_app1.
    Qed.

    Lemma app_ge :
      n >= length x ->
      nth_error (x ++ y) n = nth_error y (n - length x).
    Proof.
      apply nth_error_app2.
    Qed.

    Lemma rev :
      n < length x ->
      nth_error (rev x) n = nth_error x (length x - S n).
    Proof.
      intros n_lt_x; destruct x as [| u₀ x₀].
        contradict n_lt_x; auto with arith.
      setoid_rewrite nth_error_nth' with (d := u₀).
          f_equal; now apply rev_nth.
        now rewrite rev_length.
      lia.
    Qed.
  End Properties.

  Lemma spec :
    forall
    (A : Type)
    (x y : list A)
    (n : nat),
    OptionSpec
      (fun _ => n < length x)
      (n >= length x)
      (nth_error x n).
  Proof.
    intros.
    now destruct (nth_error x n) as [v|] eqn: nth; constructor;
      [apply Some_lt with v| apply None_ge].
  Qed.
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
        now apply Nat.nle_succ_0 in n_ge_x.
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
        contradict n_lt_x; apply Nat.nlt_0_r.
      destruct n as [| n']; simpl.
        split.
          now intros [= <-]; (repeat split);
            [auto with arith|..| destruct m as [| m']].
        destruct y as [| v₀ y₀]; intros (n_lt_x & x_eq_y & [= ->] & H).
        repeat f_equal; apply NthError.eq_iff.
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

Module Type EqAOn
  (E : EqualityType).

  Parameter eq :
    list E.t ->
    list E.t ->
    Prop.

  Section Specification.
    Variables
      (u₀ : E.t)
      (x₀ : list E.t)
      (v₀ : E.t)
      (y₀ : list E.t).

    Axiom eq_nil_nil_iff :
      eq [] [] <->
      True.

    Axiom eq_nil_cons_iff :
      eq [] (v₀ :: y₀) <->
      False.

    Axiom eq_cons_nil_iff :
      eq (u₀ :: x₀) [] <->
      False.

    Axiom eq_cons_cons_iff :
      eq (u₀ :: x₀) (v₀ :: y₀) <->
      E.eq u₀ v₀ /\ eq x₀ y₀.
  End Specification.
End EqAOn.

Module FromEqListA
  (E : EqualityType) <:
  EqAOn E.

  Definition eq :
    list E.t ->
    list E.t ->
    Prop :=
    eqlistA E.eq.

  Section Specification.
    Variables
      (u₀ : E.t)
      (x₀ : list E.t)
      (v₀ : E.t)
      (y₀ : list E.t).

    Lemma eq_nil_nil_iff :
      eq [] [] <->
      True.
    Proof.
      split; constructor.
    Qed.

    Lemma eq_nil_cons_iff :
      eq [] (v₀ :: y₀) <->
      False.
    Proof.
      split; [inversion 1| easy].
    Qed.

    Lemma eq_cons_nil_iff :
      eq (u₀ :: x₀) [] <->
      False.
    Proof.
      split; [easy| inversion 1].
    Qed.

    Lemma eq_cons_cons_iff :
      eq (u₀ :: x₀) (v₀ :: y₀) <->
      E.eq u₀ v₀ /\ eq x₀ y₀.
    Proof.
      split.
        inversion_clear 1 as [| ? ? ? ? u₀_eq_v₀ x₀_eq_y₀]; now split.
      intros (u₀_eq_v₀ & x₀_eq_y₀); now constructor.
    Qed.
  End Specification.
End FromEqListA.

Module EqAFactsOn
  (E : EqualityType)
  (Import EqA : EqAOn E).

  Module EqListA :=
    FromEqListA E.

  Lemma eq_nil :
    eq [] [].
  Proof.
    now apply eq_nil_nil_iff.
  Qed.

  Lemma eq_cons :
    forall
    (u₀ v₀ : E.t)
    (x₀ y₀ : list E.t),
    E.eq u₀ v₀ ->
    eq x₀ y₀ ->
    eq (u₀ :: x₀) (v₀ :: y₀).
  Proof.
    intros u₀ v₀ x₀ y₀ u₀_eq_v₀ x₀_eq_y₀.
    now apply eq_cons_cons_iff.
  Qed.

  Lemma eq_altdef :
    forall
    x y : list E.t,
    eq x y <->
    EqListA.eq x y.
  Proof.
    induction x as [| u₀ x₀ IHx₀]; intros [| v₀ y₀].
          now rewrite eq_nil_nil_iff, EqListA.eq_nil_nil_iff.
        now rewrite eq_nil_cons_iff, EqListA.eq_nil_cons_iff.
      now rewrite eq_cons_nil_iff, EqListA.eq_cons_nil_iff.
    now rewrite eq_cons_cons_iff, EqListA.eq_cons_cons_iff, IHx₀.
  Qed.

  Instance eq_equiv :
    Equivalence eq.
  Proof.
    pose (equiv := eqlistA_equiv E.eq_equiv).
    constructor.
        intros x; now setoid_rewrite eq_altdef.
      intros x y; now setoid_rewrite eq_altdef.
    intros x y z; now setoid_rewrite eq_altdef; transitivity y.
  Qed.

  Add Parametric Morphism : (@cons E.t) with
    signature (E.eq ==> eq ==> eq) as cons_morphism.
  Proof.
    intros u u' u_eq_u' x x' x_eq_x'.
    now rewrite eq_cons_cons_iff.
  Qed.

  Add Parametric Morphism : (@app E.t) with
    signature (eq ==> eq ==> eq) as app_morphism.
  Proof.
    intros x x' x_eq_x' y y' y_eq_y'.
    rewrite eq_altdef in x_eq_x', y_eq_y' |- *.
    now rewrite x_eq_x', y_eq_y'.
  Qed.

  Add Parametric Morphism : (@length E.t) with
    signature (eq ==> Logic.eq) as length_morphism.
  Proof.
    intros x x' x_eq_x'.
    rewrite eq_altdef in x_eq_x'; apply eqlistA_length with (1 := x_eq_x').
  Qed.

  Lemma eq_app_app_iff :
    forall
    y y' x x' : list E.t,
    length x = length x' \/ length y = length y' ->
    eq (x ++ y) (x' ++ y') <->
    eq x x' /\ eq y y'.
  Proof.
    intros y y' x.
    enough (G :
      forall
      x' : list E.t,
      length x = length x' ->
      eq (x ++ y) (x' ++ y') ->
      eq x x' /\ eq y y').
      intros x' H.
      split.
        intros e; enough (length x = length x') by (now apply G).
        destruct H as [x_eq_x'| y_eq_y']; [assumption|].
          apply plus_reg_l with (length y); rewrite y_eq_y' at 2.
          setoid_rewrite Nat.add_comm; setoid_rewrite <- app_length.
          now apply length_morphism.
      now intros (-> & ->).
    induction x as [| u₀ x₀]; intros [| u₀' x₀'] [=] e.
      enough (eq [] []) by tauto.
      now apply eq_nil_nil_iff.
    apply eq_cons_cons_iff in e as (u₀_eq_u₀' & e);
    specialize IHx₀ with (1 := H0) (2 := e) as (x₀_eq_x₀' & y_eq_y');
    change (eq (x₀ ++ y) (x₀' ++ y')) in e.
    now rewrite eq_cons_cons_iff.
  Qed.

  Lemma app_eq_nil :
    forall
    x y : list E.t,
    eq (x ++ y) [] ->
    eq x [] /\ eq y [].
  Proof.
    intros x y e.
    apply eq_app_app_iff; [| assumption].
    enough (length x = 0 /\ length y = 0) by tauto.
    rewrite <- Nat.eq_add_0, <- app_length.
    apply length_morphism with (1 := e).
  Qed.

  Lemma app_inv_head:
    forall
    x y y' : list E.t,
    eq (x ++ y) (x ++ y') ->
    eq y y'.
  Proof.
    now intros x y y'; apply eq_app_app_iff; left.
  Qed.

  Lemma app_inv_tail :
    forall
    x x' y : list E.t,
    eq (x ++ y) (x' ++ y) ->
    eq x x'.
  Proof.
    now intros y x x'; apply eq_app_app_iff; right.
  Qed.
End EqAFactsOn.

Module Type LeAOn
  (E : EqualityType)
  (Import EqA : EqAOn E).

  Parameter le :
    list E.t ->
    list E.t ->
    Prop.

  Axiom le_iff :
    forall
    x y : list E.t,
    le x y <->
    eq x y \/
    exists
    (v₀ : E.t)
    (y₀ : list E.t),
    y = v₀ :: y₀ /\
    le x y₀.
End LeAOn.

Module FromLeListA
  (E : EqualityType)
  (Import EqA : EqAOn E) <:
  LeAOn E EqA.

  Definition le
    (x y : list E.t) :
    Prop :=
    exists
    x' : list E.t,
    eq (x' ++ x) y.

  Lemma le_iff :
    forall
    x y : list E.t,
    le x y <->
    eq x y \/
    exists
    (v₀ : E.t)
    (y₀ : list E.t),
    y = v₀ :: y₀ /\
    le x y₀.
  Proof.
    intros x y.
    split.
      intros ([| u₀' x₀'] & e); [now left| right].
      destruct y as [| v₀ y₀]; [now apply eq_cons_nil_iff in e|];
      apply eq_cons_cons_iff in e as (u₀'_eq_v₀ & e);
      change (eq (x₀' ++ x) y₀) in e.
        now exists v₀, y₀; split; [| exists x₀'].
    intros [x_eq_y| (v₀ & y₀ & -> & x' & e)].
      now exists [].
    now exists (v₀ :: x'); apply eq_cons_cons_iff.
  Qed.
End FromLeListA.

Module LeAFactsOn
  (E : EqualityType)
  (Import EqA : EqAOn E)
  (Import LeA : LeAOn E EqA).

  Module EqA_Facts :=
    EqAFactsOn E EqA.

  Module LeListA :=
    FromLeListA E EqA.

  Lemma le_eq :
    forall
    x y : list E.t,
    eq x y ->
    le x y.
  Proof.
    intros x y x_eq_y; now apply le_iff; left.
  Qed.

  Lemma le_cons :
    forall
    (x : list E.t)
    (v₀ : E.t)
    (y₀ : list E.t),
    le x y₀ ->
    le x (v₀ :: y₀).
  Proof.
    intros x v₀ y₀ x_le_y₀; now apply le_iff; right; exists v₀, y₀.
  Qed.

  Lemma le_altdef :
    forall
    x y : list E.t,
    le x y <->
    LeListA.le x y.
  Proof.
    intros x; induction y as [| v₀ y₀ IHy₀]; rewrite le_iff, LeListA.le_iff.
      enough (forall (v₀ : E.t) y₀, [] <> v₀ :: y₀);
      [firstorder| intros v₀ y₀ [=]].
    now split; (intros [e| (v₀' & y₀' & [= -> ->] & x_le_y₀')];
    [left| right; exists v₀', y₀'; split; [| apply IHy₀]]).
  Qed.

  Instance le_preorder :
    PreOrder le.
  Proof.
    constructor.
      now intros x; rewrite le_altdef; exists [].
    intros x y z; setoid_rewrite le_altdef; intros (x' & H) (y' & G).
    now exists (y' ++ x'); rewrite <- app_assoc, H.
  Qed.

  Instance le_compat :
    Proper (eq ==> eq ==> iff) le.
  Proof.
    intros x x' x_eq_x' y y' y_eq_y'; setoid_rewrite le_altdef.
    enough (forall z : list E.t, eq (z ++ x) y <-> eq (z ++ x') y') by
      firstorder.
    now intros z; rewrite x_eq_x', y_eq_y'.
  Qed.

  Instance le_order :
    PartialOrder eq le.
  Proof.
    change (forall x y : list E.t, eq x y <-> le x y /\ le y x);
    intros x y; split.
      now intros ->.
    setoid_rewrite le_altdef; intros ((x' & H) & y' & G).
    enough (eq x' [] /\ eq y' []) as (x'_eq_nil & y'_eq_nil).
      now rewrite x'_eq_nil in H.
    enough (I : eq (x' ++ y') []) by now apply  EqA_Facts.app_eq_nil.
    apply  EqA_Facts.app_inv_tail with y; now rewrite <- app_assoc, G.
  Qed.
End LeAFactsOn.

Module Type NthAOn
  (E : DecidableType).

  Parameter t :
    E.t ->
    list E.t ->
    nat ->
    Prop.

  Section Specification.
    Variables
      (v u₀ : E.t)
      (x₀ : list E.t)
      (n : nat).

    Axiom nil_iff :
      t v [] n <->
      False.

    Axiom cons_O_iff :
      t v (u₀ :: x₀) O <->
      E.eq v u₀.

    Axiom cons_S_iff :
      t v (u₀ :: x₀) (S n) <->
      t v x₀ n.
  End Specification.
End NthAOn.

Module FromNth
  (E : DecidableType) <:
  NthAOn E.

  Definition t
    (v : E.t)
    (x : list E.t)
    (n : nat) :
    Prop :=
    exists
    u : E.t,
    Nth x n u /\
    E.eq v u.

  Section Properties.
    Variables
      (v u₀ : E.t)
      (x₀ : list E.t)
      (n : nat).

    Lemma nil_iff :
      t v [] n <->
      False.
    Proof.
      unfold t; setoid_rewrite Nth.nil_iff; firstorder.
    Qed.

    Lemma cons_O_iff :
      t v (u₀ :: x₀) O <->
      E.eq v u₀.
    Proof.
      split.
        now intros (u & n_to_u & v_eq_u); injection n_to_u as ->.
      now intros v_eq_u₀; exists u₀.
    Qed.

    Lemma cons_S_iff :
      t v (u₀ :: x₀) (S n) <->
      t v x₀ n.
    Proof.
      now split; intros (u & n_to_u & v_eq_u); exists u.
    Qed.
  End Properties.
End FromNth.

Module NthAFactsOn
  (E : DecidableType)
  (Import NthA : NthAOn E).

  Section Properties.
    Variables
      (v u₀ : E.t)
      (x₀ : list E.t)
      (n : nat).

    Lemma cons_O :
      E.eq v u₀ ->
      t v (u₀ :: x₀) O.
    Proof.
      apply cons_O_iff.
    Qed.

    Lemma cons_S :
      t v x₀ n ->
      t v (u₀ :: x₀) (S n).
    Proof.
      apply cons_S_iff.
    Qed.

    Lemma nil_inv :
      ~ t v [] n.
    Proof.
      unfold not; apply nil_iff.
    Qed.

    Lemma cons_O_inv :
      t v (u₀ :: x₀) O ->
      E.eq v u₀.
    Proof.
      apply cons_O_iff.
    Qed.

    Lemma cons_S_inv :
      t v (u₀ :: x₀) (S n) ->
      t v x₀ n.
    Proof.
      apply cons_S_iff.
    Qed.
  End Properties.

  Module Hints.
    #[export]
    Hint Resolve nil : nth.
    #[export]
    Hint Resolve cons_O : nth.
    #[export]
    Hint Resolve cons_S : nth.
  End Hints.
  Import Hints.

  Lemma n_lt_x_iff:
    forall
    (x : list E.t)
    (n : nat),
    n < length x <->
    (exists
    v : E.t,
    NthA.t v x n).
  Proof with firstorder with arith nth relations.
    induction x as [| u₀ x₀ IHx₀]; intros n.
      setoid_rewrite nil_iff...
    destruct n as [| n'].
      enough ((exists v, t v (u₀ :: x₀) 0) /\ 0 < length (u₀ :: x₀)) as
        (H₁ & H₂) by tauto.
      split; [exists u₀| simpl]; auto with arith nth relations.
    now simpl; setoid_rewrite cons_S_iff; rewrite <- Nat.succ_lt_mono.
  Qed.

  Lemma InA_iff:
    forall
    (v : E.t)
    (x : list E.t),
    InA E.eq v x <->
    (exists
    n : nat,
    NthA.t v x n).
  Proof with firstorder with nth.
    induction x as [| u₀ x₀ IHx₀].
      rewrite InA_nil; setoid_rewrite nil_iff...
    rewrite InA_cons, IHx₀.
    split.
      intros [v_eq_u₀| (n & NthA_v_x₀_n)];
      [exists 0| exists (S n)]...
    intros ([| n'] & NthA_v_x_n); [left| right].
      now apply cons_O_inv with x₀.
    now exists n'; apply cons_S_inv with u₀.
  Qed.

  Module FromNth :=
    FromNth E.

  Lemma FromNth_iff :
    forall
    (v : E.t)
    (x : list E.t)
    (n : nat),
    FromNth.t v x n <->
    t v x n.
  Proof.
    intros v.
    induction x as [| u₀ x₀ IHx₀]; intros n.
      now rewrite FromNth.nil_iff, nil_iff.
    destruct n as [| n'].
      now rewrite FromNth.cons_O_iff, cons_O_iff.
    now rewrite FromNth.cons_S_iff, cons_S_iff.
  Qed.

  Add Parametric Morphism : NthA.t
    with signature E.eq ==> eqlistA E.eq ==> eq ==> iff as NthA_morphism.
  Proof.
    intros v v' v_eq_v' x x' x_eq_x'.
    induction x_eq_x' as [| u₀ u₀' x₀ x₀' u₀_eq_u₀' x₀_eq_x₀' IHx₀_eq_x₀'];
      intros n.
      now rewrite 2!nil_iff.
    destruct n as [| n'].
      now rewrite 2!cons_O_iff, v_eq_v', u₀_eq_u₀'.
    rewrite 2!cons_S_iff; apply IHx₀_eq_x₀'.
  Qed.
End NthAFactsOn.

Module Type RNthAOn
  (E : DecidableType).

  Parameter t :
    E.t ->
    list E.t ->
    nat ->
    Prop.

  Section Specification.
    Variables
      (v u₀ : E.t)
      (x₀ : list E.t)
      (n : nat).

    Axiom nil_iff :
      t v [] n <->
      False.

    Axiom cons_eq_iff :
      t v (u₀ :: x₀) (length x₀) <->
      E.eq v u₀.

    Axiom cons_neq_iff :
      n <> length x₀ ->
      t v (u₀ :: x₀) n <->
      t v x₀ n.
  End Specification.
End RNthAOn.

Module FromNthA
  (E : DecidableType)
  (NthA : NthAOn E) <:
  RNthAOn E.

  Definition t
    (v : E.t)
    (x : list E.t)
    (n : nat) :
    Prop :=
    n < length x /\
    NthA.t v x (length x - S n).

  Section Properties.
    Variables
      (v u₀ : E.t)
      (x₀ : list E.t)
      (n : nat).

    Lemma nil_iff :
      t v [] n <->
      False.
    Proof.
      now unfold t; rewrite NthA.nil_iff.
    Qed.

    Lemma n_lt_x_iff :
      n < length (u₀ :: x₀) <->
      n < length x₀ \/ n = length x₀.
    Proof.
      change (length (u₀ :: x₀)) with (S (length x₀)).
      now rewrite Nat.lt_succ_r, Nat.le_lteq.
    Qed.

    Lemma cons_eq_iff :
      t v (u₀ :: x₀) (length x₀) <->
      E.eq v u₀.
    Proof.
      unfold t; rewrite Nat.sub_diag, NthA.cons_O_iff.
      enough (length x₀ < length (u₀ :: x₀)); [tauto| auto with arith].
    Qed.

    Lemma cons_neq_iff :
      n <> length x₀ ->
      t v (u₀ :: x₀) n <->
      t v x₀ n.
    Proof.
      intros n_neq_x₀; unfold t; rewrite n_lt_x_iff.
      enough (n < length x₀ -> NthA.t v (u₀ :: x₀) (length (u₀ :: x₀) - S n) <-> NthA.t v x₀ (length x₀ - S n)) by tauto.
      intros n_lt_x₀.
      replace (length (u₀ :: x₀) - S n) with (S (length x₀ - S n)).
        now rewrite NthA.cons_S_iff.
      simpl; rewrite Nat.sub_succ_r.
      now apply Nat.succ_pred, Nat.sub_gt.
    Qed.
  End Properties.
End FromNthA.

Module RFromNth
  (E : DecidableType) <:
  RNthAOn E.

  Module FromNth :=
    FromNth E.
  Module FromNthA :=
    FromNthA E FromNth.

  Include FromNthA.
End RFromNth.

Module RNthAFactsOn
  (E : DecidableType)
  (Import RNthA : RNthAOn E).

  Section Properties.
    Variables
      (v u₀ : E.t)
      (x₀ : list E.t)
      (n : nat).

    Lemma cons_eq :
      E.eq v u₀ ->
      t v (u₀ :: x₀) (length x₀).
    Proof.
      apply cons_eq_iff.
    Qed.

    Lemma cons_neq :
      n <> length x₀ ->
      t v x₀ n ->
      t v (u₀ :: x₀) n.
    Proof.
      apply cons_neq_iff.
    Qed.

    Lemma nil_inv :
      ~ t v [] n.
    Proof.
      unfold not; apply nil_iff.
    Qed.

    Lemma cons_eq_inv :
      t v (u₀ :: x₀) (length x₀) ->
      E.eq v u₀.
    Proof.
      apply cons_eq_iff.
    Qed.

    Lemma cons_neq_inv :
      n <> length x₀ ->
      t v (u₀ :: x₀) n ->
      t v x₀ n.
    Proof.
      apply cons_neq_iff.
    Qed.
  End Properties.

  Module Hints.
    #[export]
    Hint Resolve nil : nth.
    #[export]
    Hint Resolve cons_eq : nth.
    #[export]
    Hint Resolve cons_neq : nth.
  End Hints.
  Import Hints.

  Module RFromNth :=
    RFromNth E.
  Module FromNth_Facts :=
    NthAFactsOn E RFromNth.FromNth.

  Lemma RFromNth_iff :
    forall
    (v : E.t)
    (x : list E.t)
    (n : nat),
    RFromNth.t v x n <->
    t v x n.
  Proof.
    intros v.
    induction x as [| u₀ x₀ IHx₀]; intros n.
      now rewrite RFromNth.nil_iff, nil_iff.
    specialize Nat.eq_dec with n (length x₀) as
      [->| n_neq_x₀].
      now rewrite RFromNth.cons_eq_iff, cons_eq_iff.
    now rewrite RFromNth.cons_neq_iff, cons_neq_iff.
  Qed.

  Lemma n_lt_x_iff:
    forall
    (x : list E.t)
    (n : nat),
    n < length x <->
    (exists
    v : E.t,
    RNthA.t v x n).
  Proof.
    intros x n; setoid_rewrite <- RFromNth_iff.
    enough (n < length x -> exists v : E.t, RFromNth.FromNth.t v x (length x - S n)) by firstorder.
    intros n_lt_x; apply FromNth_Facts.n_lt_x_iff; auto with arith.
  Qed.

  Lemma InA_iff:
    forall
    (v : E.t)
    (x : list E.t),
    InA E.eq v x <->
    (exists
    n : nat,
    RNthA.t v x n).
  Proof.
    intros v x; rewrite FromNth_Facts.InA_iff;
    setoid_rewrite <- RFromNth_iff; unfold RFromNth.t.
    split.
      intros (n & n_to_v).
      assert (n_lt_x : n < length x).
        now apply FromNth_Facts.n_lt_x_iff; exists v.
      exists (length x - S n); split.
        apply Nat.sub_lt; auto with arith.
      enough (length x - S (length x - S n) = n) as -> by assumption.
      replace (S (length x - S n)) with (length x - n).
        symmetry; apply Minus.plus_minus.
        symmetry; apply Nat.sub_add; auto with arith.
      apply Nat.sub_succ_l with (1 := n_lt_x).
    now intros (n & n_lt_x & x_minus_n_to_v); exists (length x - S n).
  Qed.

  Add Parametric Morphism : RNthA.t
    with signature E.eq ==> eqlistA E.eq ==> eq ==> iff as RNthA_morphism.
  Proof.
    intros v v' v_eq_v' x x' x_eq_x' n.
    rewrite <- 2!RFromNth_iff; unfold RFromNth.t.
    now rewrite v_eq_v', eqlistA_length with (1 := x_eq_x'), x_eq_x'.
  Qed.

  Lemma cons_iff :
    forall
    (v u₀ : E.t)
    (x₀ : list E.t)
    (n : nat),
    t v (u₀ :: x₀) n <->
    n = length x₀ /\ E.eq v u₀ \/
    t v x₀ n.
  Proof.
    intros v u₀ x₀ n.
    enough (H : t v x₀ n -> n <> length x₀).
      specialize Nat.eq_dec with n (length x₀) as [->| n_neq_x₀];
      [rewrite cons_eq_iff| rewrite cons_neq_iff];
      firstorder.
    intros n_to_v.
    now apply Nat.lt_neq, n_lt_x_iff; exists v.
  Qed.
End RNthAFactsOn.

Module LocallySorted.
  Section Properties.
    Variables
      (A : Type)
      (R : A -> A -> Prop)
      (u₀ u₁ : A)
      (x₁ : list A).

    Lemma nil_iff :
      LocallySorted R [] <->
      True.
    Proof.
      split; constructor.
    Qed.

    Lemma cons1_iff :
      LocallySorted R [u₀] <->
      True.
    Proof.
      split; constructor.
    Qed.

    Lemma consn_iff :
      LocallySorted R (u₀ :: u₁ :: x₁) <->
      R u₀ u₁ /\
      LocallySorted R (u₁ :: x₁).
    Proof.
      split.
        now inversion_clear 1 as [| | ? ? ? LSorted_x₀ R_u₀_u₁].
      now intros (R_u₀_u₁ & LSorted_x₀); constructor.
    Qed.
  End Properties.
End LocallySorted.

Module HdRel.
  Section HdRel.
    Variables
      (A : Type)
      (R : A -> A -> Prop).

    Section Properties.
      Variables
        (v u₀ : A)
        (x₀ y : list A).

      Lemma nil_iff :
        HdRel R v [] <->
        True.
      Proof.
        split; constructor.
      Qed.

      Lemma cons_iff :
        HdRel R v (u₀ :: x₀) <->
        R v u₀.
      Proof.
        split.
          now inversion_clear 1.
        now intros R_v_u₀; constructor.
      Qed.
    End Properties.

    Lemma app :
      forall
      (w v : A)
      (x y : list A),
      HdRel R w (x ++ v :: y) <->
      HdRel R w (x ++ [v]).
    Proof.
      intros w v x y.
      now destruct x as [| u₀ x₀];
      simpl; rewrite 2!HdRel.cons_iff.
    Qed.
  End HdRel.
End HdRel.

Module Sorted.
  Section Properties.
    Variables
      (A : Type)
      (R : A -> A -> Prop)
      (u₀ : A)
      (x₀ : list A).

    Lemma nil_iff :
      Sorted R [] <->
      True.
    Proof.
      split; constructor.
    Qed.

    Lemma cons_iff :
      Sorted R (u₀ :: x₀) <->
      HdRel R u₀ x₀ /\
      Sorted R x₀.
    Proof.
      split.
        now inversion_clear 1; constructor.
      now intros (HdRel_u₀_x₀ & Sorted_x₀); constructor.
    Qed.
  End Properties.

  Section Misc.
    Variables
      (A : Type)
      (R : A -> A -> Prop).

    Lemma app :
      forall
      (v : A)
      (y x : list A),
      Sorted R (x ++ v :: y) <->
      Sorted R x /\
      HdRel (flip R) v (rev x) /\
      Sorted R (v :: y).
    Proof.
      induction x as [| u₀ x₀ IHx₀].
        rewrite nil_iff, HdRel.nil_iff; tauto.
      simpl; rewrite 2!cons_iff, IHx₀.
      enough (HdRel R u₀ (x₀ ++ v :: y) /\ HdRel (flip R) v (rev x₀)
      <-> HdRel R u₀ x₀ /\ HdRel (flip R) v (rev x₀ ++ [u₀])) by tauto.
      destruct x₀ as [| u₁ x₁]; simpl; rewrite 2!HdRel.cons_iff.
        rewrite 2!HdRel.nil_iff; tauto.
      now rewrite <- app_assoc, <- HdRel.app with (y := [u₀]).
    Qed.

    Lemma rev :
      forall
      x : list A,
      Sorted R (rev x) <->
      Sorted (flip R) x.
    Proof.
      induction x as [| u₀ x₀ IHx₀].
        now rewrite 2!nil_iff.
      simpl; rewrite app, rev_involutive, IHx₀, 2!cons_iff, HdRel.nil_iff, nil_iff;
      tauto.
    Qed.
  End Misc.
End Sorted.

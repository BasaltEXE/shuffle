Require Import
  Coq.Structures.Orders.

Require Import
  Shuffle.Misc.

Module Type IsPartialOrder
  (Import E : EqualityType)
  (Import Le : HasLe E).
  Declare Instance le_preorder : PreOrder le.
  Declare Instance le_order : PartialOrder eq le.
  Declare Instance le_compat : Proper (eq ==> eq ==> iff) le.
End IsPartialOrder.

Module Type HasPartialCmp
  (Import E : Typ).
  Parameter Inline partial_compare :
    t ->
    t ->
    option comparison.
End HasPartialCmp.

Module Type PartialCmpSpec
  (Import E : EqLt')
  (Import C : HasPartialCmp E).
  Axiom partial_compare_spec :
    forall
    x y : t,
    OptionSpec
      (CompareSpec (x == y) (x < y) (y < x))
      (x ~= y /\ ~ x < y /\ ~ y < x)
      (partial_compare x y).
End PartialCmpSpec.

Module Type HasPartialCompare
  (E : EqLt) :=
  HasPartialCmp E <+
  PartialCmpSpec E.

Module Type StrOrderFull :=
  StrOrder <+
  HasLe <+
  LeIsLtEq.

Module GenericPartialOrder
  (Import O : StrOrder').

  Definition le
    (x y : t) :
    Prop :=
    x < y \/ x == y.

  Infix "<=" := le.

  Lemma le_lteq :
    forall
    x y : t,
    x <= y <->
    x < y \/ x == y.
  Proof.
    intros x y; reflexivity.
  Qed.

  Add Parametric Morphism : le
    with signature (eq ==> eq ==> iff) as le_compat.
  Proof.
    intros x x' x_eq_x' y y' y_eq_y'.
    now unfold le; rewrite x_eq_x', y_eq_y'.
  Qed.

  Instance le_preorder : PreOrder le.
  Proof.
    unfold le; split.
      now intros x; right.
    intros x y z x_le_y y_le_z.
    destruct x_le_y as [x_lt_y| x_eq_y].
      now destruct y_le_z as [y_lt_z| y_eq_z]; left;
        [transitivity y| rewrite <- y_eq_z].
    now rewrite x_eq_y.
  Qed.

  Instance le_order : PartialOrder eq le.
  Proof.
     intros x y.
     split.
      now intros x_eq_y;
      change (le x y /\ le y x); rewrite x_eq_y.
    intros [x_le_y x_ge_y]; change (y <= x) in x_ge_y.
    destruct x_le_y as [x_lt_y| x_eq_y];
      [destruct x_ge_y as [x_gt_y| y_eq_x]|]; try easy.
    now absurd (x < x); [apply irreflexivity| transitivity y].
  Qed.
End GenericPartialOrder.

Module GenericPartialCompare
  (Import E : EqLt')
  (Import C : HasCompare E) <:
  HasPartialCompare E.

  Definition partial_compare
    (self other : t) :
    option comparison :=
    Some (compare self other).

  Lemma partial_compare_spec :
    forall
    x y : t,
    OptionSpec
      (CompareSpec (x == y) (x < y) (y < x))
      (x ~= y /\ ~ x < y /\ ~ y < x)
      (partial_compare x y).
  Proof.
    intros x y; constructor; apply compare_spec.
  Qed.
End GenericPartialCompare.

Module GenericBooleanFunctions
  (Import O : StrOrderFull)
  (Import C : HasPartialCompare O).

  Definition eqb
    (self other : t) :
    bool :=
    match C.partial_compare self other with
    | Some Eq => true
    | _ => false
    end.

  Lemma lt_impl_neq :
    forall
    x y : O.t,
    O.lt x y ->
    O.eq x y ->
    False.
  Proof.
    intros x y x_lt_y x_eq_y.
    contradict x_lt_y; rewrite x_eq_y; apply irreflexivity.
  Qed.

  Lemma gt_impl_neq :
    forall
    x y : O.t,
    O.lt y x ->
    O.eq x y ->
    False.
  Proof.
    intros x y x_gt_y x_eq_y.
    now symmetry in x_eq_y; apply lt_impl_neq with y x.
  Qed.

  Lemma lt_impl_ngt :
    forall
    x y : O.t,
    O.lt x y ->
    O.lt y x ->
    False.
  Proof.
    intros x y x_lt_y x_gt_y.
    now absurd (lt x x); [apply irreflexivity| transitivity y].
  Qed.

  #[local]
  Hint Immediate lt_impl_neq gt_impl_neq lt_impl_ngt : partial.

  Lemma eqb_eq :
    forall
    x y : t,
    eqb x y = true <->
    eq x y.
  Proof.
    intros x y; unfold eqb.
    specialize partial_compare_spec with x y as [cmp_x_y [x_eq_y| x_lt_y| x_gt_y]|].
    2, 3, 4: now split; [intros [=]| intros x_eq_y; exfalso; eauto with partial].
    easy.
  Qed.

  Definition ltb
    (self other : t) :
    bool :=
    match C.partial_compare self other with
    | Some Lt => true
    | _ => false
    end.

  Lemma ltb_lt :
    forall
    x y : t,
    ltb x y = true <->
    lt x y.
  Proof.
    intros x y; unfold ltb.
    specialize C.partial_compare_spec with x y as [cmp_x_y [x_eq_y| x_lt_y| x_gt_y]|].
    1, 3, 4: now split; [intros [=]| intros x_lt_y; exfalso; eauto with partial].
    easy.
  Qed.

  Definition leb
    (self other : t) :
    bool :=
    match C.partial_compare self other with
    | Some (Lt | Eq) => true
    | _ => false
    end.

  Lemma leb_le :
    forall
    x y : t,
    leb x y = true <->
    le  x y.
  Proof.
    intros x y; unfold leb; rewrite le_lteq.
    specialize C.partial_compare_spec with x y as [cmp_x_y [x_eq_y| x_lt_y| x_gt_y]|].
      1, 2: tauto.
    1, 2: now split; [intros [=]| intros [x_lt_y| x_eq_y]; exfalso; eauto with partial].
  Qed.
End GenericBooleanFunctions.

Module ReflectSpec
  (Import O : EqLtLe')
  (Import F : HasBoolOrdFuns' O)
  (Import S : BoolOrdSpecs O F).

  Lemma eqb_spec :
    forall
    x y : t,
    Bool.reflect (x == y) (x =? y).
  Proof.
    intros x y.
    apply Bool.iff_reflect; symmetry; apply eqb_eq.
  Qed.

  Lemma ltb_spec :
    forall
    x y : t,
    Bool.reflect (x < y) (x <? y).
  Proof.
    intros x y.
    apply Bool.iff_reflect; symmetry; apply ltb_lt.
  Qed.

  Lemma leb_spec :
    forall
    x y : t,
    Bool.reflect (x <= y) (x <=? y).
  Proof.
    intros x y.
    apply Bool.iff_reflect; symmetry; apply leb_le.
  Qed.
End ReflectSpec.

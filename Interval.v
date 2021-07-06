Set Implicit Arguments.

Require Import
  Coq.Structures.OrdersFacts
  Coq.Structures.GenericMinMax
  Coq.Program.Program.

Import Coq.Bool.Bool(
  not_true_iff_false,
  orb_true_iff,
  andb_true_iff,
  andb_false_iff).

Require Import
  Shuffle.Misc
  Shuffle.Orders.

Module Type IntervalType :=
  StrOrder <+
  HasLe <+
  LeIsLtEq <+
  IsPartialOrder <+
  HasBoolOrdFuns <+
  BoolOrdSpecs <+
  HasPartialCompare.

Module Interval
  (O : OrderedTypeFull)
  (F : HasBoolOrdFuns' O)
  (S : BoolOrdSpecs O F)
  (M : HasMinMax O) <:
  IntervalType.

  Module Facts :=
    O <+ OrderedTypeFullFacts O.
  Module MinMaxProperties :=
    GenericMinMax.MinMaxProperties O M.
  Module BoolOrderFacts.
    Include OrdersFacts.BoolOrderFacts O O F Facts S.
  End BoolOrderFacts.

  Record Interval :
    Type := {
      left_endpoint : O.t;
      right_endpoint : O.t;
      ok : O.le left_endpoint right_endpoint;
    }.

  Definition t :
    Type :=
    Interval.

  Definition eq
    (self other : t) :
    Prop :=
    O.eq self.(left_endpoint) other.(left_endpoint) /\
    O.eq self.(right_endpoint) other.(right_endpoint).

  Instance eq_equiv :
    Equivalence eq.
  Proof with Facts.iorder.
    unfold eq; split.
        intros x...
      intros x y x_eq_y...
    intros x y z x_eq_y y_eq_z...
  Qed.

  Add Parametric Morphism : left_endpoint
    with signature eq ==> O.eq as left_endpoint_compat.
  Proof.
    now unfold eq; intros x y x_eq_y.
  Qed.

  Add Parametric Morphism : right_endpoint
    with signature eq ==> O.eq as right_endpoint_compat.
  Proof.
    now unfold eq; intros x y x_eq_y.
  Qed.

  Definition lt
    (self other : t) :
    Prop :=
    O.lt self.(right_endpoint) other.(left_endpoint).

  Instance lt_strorder :
    StrictOrder lt.
  Proof with Facts.iorder.
    unfold lt; split.
      intros [x_left x_right Ok_x];
      change (~ O.lt x_right x_left)...
    intros [x_left x_right Ok_x] [y_left y_right Ok_y] [z_left z_right Ok_z]...
  Qed.

  Add Parametric Morphism : lt
    with signature (eq ==> eq ==>iff) as lt_compat.
  Proof with Facts.iorder.
    unfold eq, lt; intros x x' x_eq_x' y y' y_eq_y'...
  Qed.

  Include GenericPartialOrder.

  Definition eqb
    (self other : t) :
    bool :=
    (F.eqb self.(left_endpoint) other.(left_endpoint) &&
    F.eqb self.(right_endpoint) other.(right_endpoint))%bool.

  Lemma eqb_eq :
    forall
    x y : t,
    eqb x y = true <->
    eq x y.
  Proof.
    now intros x y; unfold eqb; rewrite andb_true_iff, 2! S.eqb_eq.
  Qed.

  Lemma eq_dec :
    forall
    x y : t,
    {eq x y} + {~ eq x y}.
  Proof.
    intros x y.
    now destruct (eqb x y) eqn: eqb_x_y; [left| right];
    rewrite <- eqb_eq, ?not_true_iff_false.
  Qed.

  Definition ltb
    (self other : t) :
    bool :=
    F.ltb self.(right_endpoint) other.(left_endpoint).

  Lemma ltb_lt :
    forall
    x y : t,
    ltb x y = true <->
    lt x y.
  Proof.
    now intros x y; unfold ltb; rewrite S.ltb_lt.
  Qed.

  Definition leb
    (self other : t) :
    bool :=
    ltb self other || eqb self other.

  Lemma leb_le :
    forall
    x y : t,
    leb x y = true <->
    le x y.
  Proof.
    now intros x y; unfold leb; rewrite orb_true_iff, ltb_lt, eqb_eq.
  Qed.

  Definition partial_compare
    (x y : t) :
    option comparison :=
    if ltb x y then Some Lt else
    if ltb y x then Some Gt else
    if eqb x y then Some Eq else
    None.

  Lemma partial_compare_spec :
    forall
    x y : t,
    OptionSpec
      (CompareSpec (eq x y) (lt x y) (lt y x))
      (~ eq x y /\ ~ lt x y /\ ~ lt y x)
      (partial_compare x y).
  Proof.
    intros x y; unfold partial_compare.
    destruct (ltb x y) eqn: ltb_x_y;
    [| destruct (ltb y x) eqn: ltb_y_x;
    [| destruct (eqb x y) eqn: eqb_x_y]];
    rewrite <- ?not_true_iff_false, ?eqb_eq, ?ltb_lt in * |-;
    now do 2 constructor.
  Qed.

  Program Definition replace_left_endpoint
    (self : t)
    (x : O.t | O.le x self.(right_endpoint)) :
    t :=
    {|
      left_endpoint := x;
      right_endpoint := self.(right_endpoint);
    |}.

  Program Definition replace_right_endpoint
    (self : t)
    (y : O.t | O.le self.(left_endpoint) y) :
    t :=
    {|
      left_endpoint := self.(left_endpoint);
      right_endpoint := y;
    |}.

  Notation Contains
    self
    n :=
    (O.le self.(left_endpoint) n /\ O.le n self.(right_endpoint))
    (only parsing).

  Add Parametric Morphism : (fun (self : t) (n : O.t) => Contains self n)
    with signature eq ==> O.eq ==> iff as Contains_compat.
  Proof.
    intros self other self_eq_other n m m_eq_n.
    now rewrite m_eq_n, self_eq_other.
  Qed.

  Lemma Contains_left_endpoint :
    forall
    self : t,
    Contains self (left_endpoint self).
  Proof.
    intros self; split; (reflexivity || apply ok).
  Qed.

  Lemma Contains_right_endpoint :
    forall
    self : t,
    Contains self (right_endpoint self).
  Proof.
    intros self; split; (reflexivity || apply ok).
  Qed.

  Program Definition contains
    (self : t)
    (n : O.t) :
    {b : bool | Contains self n <-> b = true} :=
    (F.leb self.(left_endpoint) n && F.leb n self.(right_endpoint))%bool.
  Next Obligation.
    now rewrite andb_true_iff, 2!S.leb_le.
  Defined.

  Definition Contains_dec :
    forall
    (self : t)
    (n : O.t),
    {Contains self n} + {~ Contains self n}.
  Proof.
    intros self n.
    now specialize contains with self n as ([|] & H); [left| right]; rewrite H.
  Qed.

  Lemma not_Contains_iff :
    forall
    (self : t)
    (n : O.t),
    ~ Contains self n <->
    O.lt n self.(left_endpoint) \/ O.lt self.(right_endpoint) n.
  Proof.
    intros self n.
    specialize Facts.le_or_gt with self.(left_endpoint) n as [H| H];
    Facts.iorder.
  Qed.

  Lemma iff_Contains_iff :
    forall
    self other : t,
    (forall
    n : O.t,
    Contains self n <-> Contains other n) <->
    eq self other.
  Proof.
    intros self other.
    split.
      intros H; split; apply antisymmetry;
      (apply H; split; (reflexivity || apply ok)).
    now intros (H₁ & H₂) n; rewrite H₁, H₂.
  Qed.

  Program Definition intersection
    (self other : t) :
    {result : option t |
      OptionSpec
        (fun interval : t =>
        forall n : O.t,
        Contains interval n <->
        Contains self n /\ Contains other n)
        (forall n : O.t,
        ~ Contains self n \/ ~ Contains other n)
        result} :=
    if dec (negb (ltb self other) && negb (ltb other self))%bool then
    Some {|
      left_endpoint := M.max self.(left_endpoint) other.(left_endpoint);
      right_endpoint := M.min self.(right_endpoint) other.(right_endpoint);
    |} else
    None.
  Next Obligation.
    pose (Ok_self := self.(ok)); pose (Ok_other := other.(ok)).
    enough (O.le (left_endpoint other) (right_endpoint self) /\
    O.le (left_endpoint self) (right_endpoint other)) by
      (rewrite MinMaxProperties.max_lub_iff, 2!MinMaxProperties.min_glb_iff;
      Facts.iorder).
    now rewrite <- !S.leb_le, 2!BoolOrderFacts.leb_antisym,
      <- andb_true_iff.
  Defined.
  Next Obligation.
    constructor; intros n; simpl.
    enough (O.le (left_endpoint other) (right_endpoint self) /\
    O.le (left_endpoint self) (right_endpoint other)) by
      (rewrite MinMaxProperties.max_lub_iff, MinMaxProperties.min_glb_iff;
      tauto).
    now rewrite <- !S.leb_le, 2!BoolOrderFacts.leb_antisym,
      <- andb_true_iff.
  Defined.
  Next Obligation.
    constructor; intros n.
    assert (O.lt self.(right_endpoint) other.(left_endpoint) \/ O.lt other.(right_endpoint) self.(left_endpoint)) as H.
      now rewrite <- 2!BoolOrderFacts.leb_gt, 2!BoolOrderFacts.leb_antisym,
        <- andb_false_iff.
    enough (~ (Contains self n /\ Contains other n)) as H'.
      specialize Contains_dec with self n; tauto.
    intros (Contains_self_n & Contains_other_n); Facts.iorder.
  Defined.
End Interval.

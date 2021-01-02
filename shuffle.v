Set Implicit Arguments.

Require Import Coq.Lists.List.
Require Export MSetInterface OrdersFacts OrdersLists.

Require Import Coq.MSets.MSetFacts Coq.MSets.MSetProperties.

Require Import  Coq.Classes.Morphisms_Prop.

Import ListNotations.

Inductive Card(Key Owner: Type) : Type :=
| Talon: Key -> Card Key Owner
| Assigned: Owner -> Card Key Owner.

Module test (Key : OrderedType) (Owner: DecidableType).

Module Positions (M: WSetsOn Owner).

Definition positions: list (Card Key.t Owner.t) -> nat -> M.t.
Proof.
  intros cards.
  induction cards as [| [key| owner] tail IHtail]; intros index.
Admitted.

End Positions.


Module Owners (M : WSetsOn Owner).

Module Import Facts := WFactsOn Owner M.
Module Import Properties := WPropertiesOn Owner M.

Definition owners_helper : list (Card Key.t Owner.t) -> M.t -> list Owner.t.
Proof.
  intros cards.
  induction cards as [| [key| owner] tail IHtail]; intros seen.
    exact [].
  exact (IHtail seen).
  exact (if M.mem owner seen then IHtail seen else owner:: IHtail (M.add owner seen)).
Defined.

Definition owners: list (Card Key.t Owner.t) ->list Owner.t :=
fun cards => owners_helper cards M.empty.

Definition owners_subset : forall (cards: list (Card Key.t Owner.t)) (seen seen' : M.t), M.Subset seen seen' -> forall owner, In owner (owners_helper cards seen') -> In owner (owners_helper cards seen).
Proof.
  intros cards.
  induction cards as [| [head_key| head_owner] tail IHtail]; intros seen seen' seen_le_seen' owner.
      easy.
    now apply IHtail.
  simpl.
  destruct (M.mem head_owner seen) eqn: mem_head_seen.
    assert (M.mem head_owner seen' = true) as ->.
      rewrite M.mem_spec.
      apply seen_le_seen'.
      now rewrite <- M.mem_spec.
    now apply IHtail.
  destruct (M.mem head_owner seen') eqn: mem_head_seen'.  
    intros In_owner_seen'.
    right.
    apply IHtail with seen'.
      apply subset_add_3.
        now apply M.mem_spec.
      assumption.
    assumption.
  simpl.
  intros H.
  destruct H.
    now left.
  right.
  apply IHtail with (M.add head_owner seen').
    simpl.
    now apply add_s_m.
  assumption.
Defined.


Definition helper_complete : forall (cards: list (Card Key.t Owner.t)) (seen: M.t) (owner : Owner.t), ~ M.In owner seen -> In owner (owners_helper cards seen) <-> In (Assigned Key.t owner) cards.
Proof.
  induction cards as [| [head_key| head_owner] tail IHtail]; intros seen owner In_owner_seen.
      reflexivity.
    simpl.
    assert (In (Assigned Key.t owner) (Talon Owner.t head_key :: tail) <-> In (Assigned Key.t owner) tail) as ->.
      split.
        destruct 1 as [owner_eq_head| In_owner_tail].
          discriminate owner_eq_head.
        assumption.
      intros In_owner_tail.
      now right.
    now apply IHtail.
  simpl.
  split.
    destruct (M.mem head_owner seen) eqn: mem_head_owner_seen.
      intro In_owner_tail.
      right.
      now apply IHtail with seen.
    simpl.
    destruct 1 as [->| In_owner_tail].
      left.
      now f_equal.
    destruct (Owner.eq_dec owner head_owner).
      left.
      admit.
    right.
    apply IHtail with (seen := seen).
      assumption.
    apply owners_subset with (seen' := (M.add head_owner seen)).
      now apply subset_add_2.
    assumption.
  destruct 1 as [head_owner_eq_owner| In_owner_tail].
    injection head_owner_eq_owner as ->.
    destruct (M.mem owner seen) eqn: mem_owner_seen.
      now rewrite M.mem_spec in mem_owner_seen.
    now left.
  simpl.
  destruct (M.mem head_owner seen) eqn: mem_head_owner_seen.
    now apply IHtail.
  (*specialize (IHtail seen owner In_owner_seen).*)
  destruct (Owner.eq_dec owner head_owner) as [owner_eq_head_owner| owner_neq_head_owner].
    left.
    admit.
  right.
  assert (In owner (owners_helper tail seen)).
    now rewrite IHtail.
  rewrite (IHtail (M.add head_owner seen) owner).
    assumption.
  intros H'.
  rewrite M.add_spec in H'.
  destruct H' as [owner_eq_head_owner| In_owner_seen'].
    admit.
  admit.
Admitted.

Definition complete : forall (cards: list (Card Key.t Owner.t))(owner : Owner.t), In owner (owners cards) <-> In (Assigned Key.t owner) cards.
Admitted.


End Owners.


Definition owners : list (Card Key.t Owner.t) -> list Owner.t.
Proof.
  intros cards.
  induction cards as [| head tail IHtail].
    exact [].
  destruct head as [key| owner].
    exact IHtail.
  exact (owner :: IHtail).
Defined.

End test.



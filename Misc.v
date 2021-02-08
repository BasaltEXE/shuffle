Set Implicit Arguments.

Inductive OptionSpec (A : Type) (P : A -> Prop) (Q : Prop) : option A -> Prop :=
| OptionSpec_Some : forall u : A, P u -> OptionSpec P Q (Some u)
| OptionSpec_None : Q -> OptionSpec P Q None.
#[global]
Hint Constructors OptionSpec : core.

Lemma OptionSpec_impl : forall
  (A : Type)
  (P P' : A -> Prop)
  (Q : Prop)
  (o : option A),
  (forall a : A, P a -> P' a) ->
  OptionSpec P Q o ->
  OptionSpec P' Q o.
Proof.
  now intros A P P' Q o P_impl_P' [a P_a| q];
    [left; apply P_impl_P'| right].
Qed.

Section Option.
  Variables
    (A B : Type).

  Definition bind
    (mx : option A)
    (f : A -> option B) :
    option B :=
      match mx with
      | Some x => f x
      | None => None
      end.

  Definition then'
    (mx : option A)
    (my : option B) :
    option B :=
      bind mx (fun _ => my).

  Definition ret
    (a : A) :
    option A :=
      Some a.
End Option.

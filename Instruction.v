Require Import Coq.Structures.Equalities Coq.Structures.EqualitiesFacts.
Require Import Coq.Classes.RelationPairs.

Module Make (Opcode Operand : DecidableType) <: DecidableType.
  Include PairDecidableType Opcode Operand.

  Definition opcode (self : t) : Opcode.t :=
    fst self.
  Definition operand (self : t) : Operand.t :=
    snd self.

  Lemma neq_iff (self other : t) : ~ eq self other <-> ~ Opcode.eq (opcode self) (opcode other) \/ ~ Operand.eq (operand self) (operand other).
  Proof.
    firstorder using Opcode.eq_dec, Operand.eq_dec.
  Qed.

  Lemma neq_opcode (self other : t) : ~ Opcode.eq (opcode self) (opcode other) -> ~ eq self other.
  Proof.
    firstorder.
  Qed.

  Lemma neq_operand (self other : t) : ~ Operand.eq (operand self) (operand other) -> ~ eq self other.
  Proof.
    firstorder.
  Qed.

  Lemma neq_eq_opcode (self other : t) : Opcode.eq (opcode self) (opcode other) -> ~ eq self other <-> ~ Operand.eq (operand self) (operand other).
  Proof.
    firstorder.
  Defined.

  Lemma neq_eq_operand (self other : t) : Operand.eq (operand self) (operand other) -> ~ eq self other <-> ~ Opcode.eq (opcode self) (opcode other).
  Proof.
    firstorder.
  Defined.

  Lemma eq_opcode (self other : t) : Opcode.eq (opcode self) (opcode other) -> eq self other <-> Operand.eq (operand self) (operand other).
  Proof.
    firstorder.
  Defined.

  Lemma eq_operand (self other : t) : Operand.eq (operand self) (operand other) -> eq self other <-> Opcode.eq (opcode self) (opcode other).
  Proof.
    firstorder.
  Defined.
End Make.

Require Import Coq.Structures.Equalities.
Require Import Coq.Classes.RelationPairs.

Module Instruction (Opcode Operand : DecidableType) <: DecidableType.
  Definition t : Type :=
    Opcode.t * Operand.t.

  Definition opcode (self : t) : Opcode.t :=
    fst self.
  Definition operand (self : t) : Operand.t :=
    snd self.

  Definition eq (self other : t) : Prop :=
    Opcode.eq (opcode self) (opcode other) /\ Operand.eq (operand self) (operand other).

  Instance eq_equiv : Equivalence eq :=
    RelProd_Equivalence _ _ _ _.

  Lemma eq_dec (self other : t) : {eq self other} + {~ eq self other}.
  Proof.
    destruct (Opcode.eq_dec (opcode self) (opcode other)) as [opcode_eq| opcode_neq];
    [destruct (Operand.eq_dec (operand self) (operand other)) as [operand_eq| operand_neq]|];
    firstorder.
  Qed.

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
End Instruction.

Require Import Ring_theory BinPos BinPosDef Arith.

Check Ring_theory.pow_pos.

Check positive.

Print positive.

Check Pos.to_nat.

Check Pos.of_nat.

Check Ring_theory.ring_theory.

Check Ring_theory.almost_ring_theory.

Goal (
    Ring_theory.almost_ring_theory
      0 1 Nat.add Nat.mul Nat.sub (fun n => 0) eq
  ).
Proof.
  constructor.
  - reflexivity.
  - apply Nat.add_comm.
  - apply Nat.add_assoc.
  - apply Nat.mul_1_l.
  - apply Nat.mul_0_l.
  - apply Nat.mul_comm.
  - apply Nat.mul_assoc.
  - apply Nat.mul_add_distr_r.
  - apply Nat.mul_0_r.

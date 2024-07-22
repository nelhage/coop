Require Import BinPos.

Check positive.

Check (6%positive).
Check N0.

Check Pos.to_nat (1~1~0)%positive.

Check 1+1.

Check ((xI xH) + (xI (xO xH))) % positive.

(* Bind Scope positive_scope with positive. *)

Fail Check ((xI xH) + (xI (xO xH))).

Check ((xI xH) + (xI (xO xH))) : positive.

Print N.

Fail Check (Npos (xI xH) + Npos (xI (xO xH))) : N.

Require Import BinNat.

Check (Npos (xI xH) + Npos (xI (xO xH))) : N.

Fixpoint ack (m : nat) : nat -> nat :=
  fix ack' n : nat  :=
    match (m, n) with
    | (O, n)    => S n
    | (S m', O) => ack m' 1
    | (S m', S n') => ack m' (ack' n')
    end.

Fixpoint half n :=
  match n with
  | O => O
  | S O => O
  | S (S n) => S (half n)
  end.

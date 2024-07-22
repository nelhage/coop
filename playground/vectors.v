Require Import Field_theory.

Section Definitions.
  Variable F : Type.
  Variable V : Type.

  Declare Scope F_scope.
  Bind Scope F_scope with F.
  Delimit Scope F_scope with field.

  Declare Scope V_scope.
  Bind Scope V_scope with V.
  Delimit Scope V_scope with vector.
  Open Scope V_scope.

  Variable (fO fI : F) (fadd fmul fsub: F->F->F) (fopp : F->F).
  Variable (fdiv : F->F->F) (finv : F->F).
  (* Variable feq : F -> F -> Prop. *)

  Notation "0" := fO : F_scope.
  Notation "1" := fI : F_scope.
  Infix "+" := fadd : F_scope.
  Infix "-" := fsub : F_scope.
  Infix "*" := fmul : F_scope.
  Infix "/" := fdiv : F_scope.
  Notation "- x" := (fopp x) : F_scope.
  Notation "/ x" := (finv x) : F_scope.
  Infix "==" := eq (at level 70, no associativity) : F_scope.

  Variable (vO vI : V) (vadd vsub: V->V->V) (vopp : V->V).
  Variable (vscale : F->V->V).
  (* Variable veq : V -> V -> Prop. *)

  Notation "0" := vO : V_scope.
  Notation "1" := vI : V_scope.
  Infix "+" := vadd : V_scope.
  Infix "-" := vsub : V_scope.
  Infix "*" := vscale : V_scope.
  Notation "- x" := (vopp x) : V_scope.
  Infix "==" := eq (at level 70, no associativity) : V_scope.

  Record vector_space_theory : Prop := mk_vst {
    Vadd_comm   : forall x y, x + y == y + x;
    Vadd_assoc  : forall x y z, x + (y + z) == (x + y) + z;
    Vadd_0_l    : forall x, 0 + x == x;
    Vopp_def    : forall x, x + (- x) == 0;
    Vmul_1_l    : forall x, 1 * x == x;

    Vdistr_r    : forall x y z, z * (x + y) == z*x + z*y;
    Vsub_def    : forall x y, x - y == x + -y;
 }.

  Section VectorSpace.

  Variable Vth : vector_space_theory.

  (* 1.26: Uniqueness of 0 *)
  Lemma Vzero_unique x : (forall y, x+y == y) -> x == 0.
  Proof using Vth.
    intros y.
    set (Vth.(Vadd_0_l) x) as x_plus0_x.
    rewrite <- x_plus0_x.
    rewrite (Vadd_comm Vth).
    rewrite -> (y 0).
    reflexivity.
  Qed.

  Lemma Vadd_0_r x : x + 0 == x.
  Proof using Vth.
    rewrite (Vadd_comm Vth).
    apply (Vadd_0_l Vth).
  Qed.

  Lemma Vx_sub_x x : x - x = 0.
  Proof using Vth.
    rewrite -> (Vsub_def Vth).
    rewrite -> (Vopp_def Vth).
    reflexivity.
  Qed.

  (* 1.27: Uniqueness of inverse *)
  Lemma Vopp_unique x y : x+y == 0 -> y == - x.
  Proof using Vth.
    intros.
    apply f_equal with (f := fun z => z  - x) in H.
    rewrite <- (Vopp_def Vth x) in H.
    rewrite -> (Vadd_comm Vth x y) in H.
    repeat rewrite (Vsub_def Vth) in H.
    rewrite <- (Vadd_assoc Vth) in H.
    rewrite (Vopp_def Vth) in H.
    rewrite (Vadd_0_l Vth) in H.
    rewrite (Vadd_0_r) in H.
    apply H.
  Qed.
  End VectorSpace.
End Definitions.

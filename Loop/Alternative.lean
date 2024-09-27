import Mathlib.Data.Vector.Defs
import Mathlib.Data.List.Basic

/-!
# The Loop programming language

The goal of this file is to formally define the semantics of the Loop
programming language, define what Loop-computable functions are, and prove that
Loop-computable is the same as primitive recursive.
-/

namespace Loop


inductive Instruction where
  | clear_var : Nat → Instruction
  | increment_var : Nat → Instruction
  | loop_var : Nat → List Instruction → Instruction
open Instruction


notation "CLEAR X " n:68 => clear_var n
notation "INC X " n:68 => increment_var n
notation "LOOP X " n " DO " ls:68 => loop_var n ls

abbrev END : List Instruction := []


-- /- A Loop program is a list of instructions. -/
def Program := List Instruction

-- example : Program := END

def example_1 : Program :=
  LOOP X 1 DO (
    LOOP X 2 DO (
      INC X 0     ::
    END)          ::
  END)            ::
  END

abbrev VarState := List Nat


def value_at (xs : VarState) (k : Nat) : Nat := xs.getD k 0

example : value_at [3, 1, 5] 2 = 5 := rfl
example : value_at [3, 1, 5] 7 = 0 := rfl

def clear_value (xs : VarState) (k : Nat) : VarState := xs.set k 0

example : clear_value [3, 1, 5] 2 = [3, 1, 0] := rfl

def inc_value (xs : VarState) (k : Nat) : VarState := xs.set k (value_at xs k + 1)

example : inc_value [3, 1, 5] 2 = [3, 1, 6] := by rfl

def init_state (v : Mathlib.Vector Nat n) : VarState := 0 :: v.toList

mutual
  def lines_of_code : Program → Nat
    | [] => 0
    | .clear_var _ :: tail => 1 + lines_of_code tail
    | .increment_var _ :: tail => 1 + lines_of_code tail
    | loop :: tail => lines_of_code_instruction loop + lines_of_code tail

  def lines_of_code_instruction : Instruction → Nat
    | .loop_var _ inner => 1 + lines_of_code inner
    | _ => 1
end

attribute [local simp] lines_of_code lines_of_code_instruction

example : lines_of_code example_1 = 3 := rfl

def execution_from_state (xs : VarState) (p : Program) : VarState :=
  let rec loop_n_times : Nat → VarState → Program → VarState
  | 0, xs, _ => xs
  | n + 1, xs, p => loop_n_times n (execution_from_state xs p) p
  termination_by n _ p => (lines_of_code p, n)

  match p with
  | [] => xs
  | .clear_var k      :: tail =>
    execution_from_state (clear_value xs k) tail
  | .increment_var k  :: tail =>
    execution_from_state (inc_value xs k) tail
  | .loop_var k inner :: tail =>
    execution_from_state (loop_n_times (value_at xs k) xs inner) tail
termination_by (lines_of_code p, 0)
open execution_from_state


def nary_program_function (p : Program) (n : Nat) (v : Mathlib.Vector Nat n) : Nat :=
  value_at (execution_from_state (init_state v) p) 0

notation "⟦ " p " ⟧^(" n ") " => nary_program_function p n

example : ⟦ example_1 ⟧^(2) ⟨[11, 11], rfl⟩ = 121 := by
  simp [nary_program_function, init_state, example_1, execution_from_state, loop_n_times, value_at, inc_value, clear_value]


def loop_computable (f : Mathlib.Vector Nat n → Nat) : Prop :=
  ∃ p : Program, ⟦ p ⟧^(n) = f

-- -- -------
def highest_var : Program → Nat
  | [] => 0
  | clear_var k :: tail =>
    have : lines_of_code tail < lines_of_code (clear_var k :: tail) := by simp
    max k (highest_var tail)
  | increment_var k :: tail =>
    have : lines_of_code tail < lines_of_code (increment_var k :: tail) := by simp
    max k (highest_var tail)
  | loop_var k inner :: tail =>
    have : lines_of_code inner < lines_of_code (loop_var k inner :: tail) := by simp_arith
    have : lines_of_code tail < lines_of_code (loop_var k inner :: tail) := by simp_arith
    max k (max (highest_var inner) (highest_var tail))
termination_by p => lines_of_code p

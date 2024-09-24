import Mathlib.Data.Vector.Defs

/-!
# The Loop programming language

The goal of this file is to formally define the semantics of the Loop
programming language, define what Loop-computable functions are, and prove that
Loop-computable is the same as primitive recursive.
-/

namespace Loop

structure Var where
  X : Nat

abbrev X₀ : Var := ⟨0⟩

inductive Instruction where
  | clear_var : Var → Instruction
  | increment_var : Var → Instruction
  | loop_var : Var → List Instruction → Instruction
open Instruction


notation "CLEAR X " n:68 => clear_var ⟨n⟩
notation "INC X " n:68 => increment_var ⟨n⟩
notation "LOOP X " n " DO " ls:68 => loop_var ⟨n⟩ ls

abbrev END : List Instruction := []


/- A Loop program is a list of instructions. -/
def Program := List Instruction

example : Program := END

def example_1 : Program :=
  LOOP X 1 DO (
    LOOP X 2 DO (
      INC X 0     ::
    END)          ::
  END)            ::
  END

def VarState := List Nat


def Var.value_at : VarState → Var → Nat
  | xs, ⟨n⟩ => xs.getD n 0

example : Var.value_at [3, 1, 5] ⟨2⟩ = 5 := rfl
example : Var.value_at [3, 1, 5] ⟨7⟩ = 0 := rfl

def Var.clear_value : VarState → Var → VarState
  | xs, ⟨n⟩ => xs.set n 0

example : Var.clear_value [3, 1, 5] ⟨2⟩ = [3, 1, 0] := rfl

def Var.inc_value : VarState → Var → VarState
  | xs, v@⟨n⟩ => xs.set n (v.value_at xs + 1)

example : Var.inc_value [3, 1, 5] ⟨2⟩ = [3, 1, 6] := by rfl

def init_state (v : Mathlib.Vector Nat n) : VarState := match v with
  | ⟨xs, _⟩ => 0 :: xs

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

example : lines_of_code example_1 = 3 := rfl

mutual
    def loop_n_times : Nat → VarState  → Program → VarState
      | 0, xs, _ => xs
      | n + 1, xs, p => loop_n_times n (execution_from_state xs p) p
    termination_by n _ p => (lines_of_code p, n)

    def execution_from_state (xs : VarState) : Program → VarState
    | [] => xs
    | .clear_var v      :: tail =>
      have : lines_of_code tail < lines_of_code (clear_var v :: tail) := by
        simp [lines_of_code]
      execution_from_state (v.clear_value xs) tail
    | .increment_var v  :: tail =>
      have : lines_of_code tail < lines_of_code (increment_var v :: tail) := by
        simp [lines_of_code]
      execution_from_state (v.inc_value xs) tail
    | .loop_var v inner :: tail =>
      have : lines_of_code inner < lines_of_code (loop_var v inner :: tail) := by
        simp_arith [lines_of_code, lines_of_code_instruction]
      have : lines_of_code tail < lines_of_code (loop_var v inner :: tail) := by
        simp_arith [lines_of_code, lines_of_code_instruction]
      execution_from_state (loop_n_times (v.value_at xs) xs inner) tail
    termination_by p => (lines_of_code p, 0)
end

def nary_program_function (p : Program) (n : Nat) (v : Mathlib.Vector Nat n) : Nat :=
  X₀.value_at (execution_from_state (init_state v) p)

notation "⟦ " p " ⟧^(" n ") " => nary_program_function p n

example : ⟦ example_1 ⟧^(2) ⟨[11, 11], rfl⟩ = 121 := by
  simp [nary_program_function, init_state, example_1, execution_from_state, loop_n_times, Var.value_at, Var.inc_value, Var.clear_value]


def loop_computable (f : Mathlib.Vector Nat n → Nat) : Prop :=
  ∃ p : Program, ⟦ p ⟧^(n) = f

-------

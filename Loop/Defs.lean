/-
Copyright: TODO
Authors: Darío Silva Rodríguez
-/

import Mathlib.Data.Vector.Defs
import Mathlib.Data.Vector.Basic
import Mathlib.Computability.Primrec

namespace Loop

abbrev VectNat := Mathlib.Vector Nat

inductive Program where
  | clear_var : Nat → Program
  | increment_var : Nat → Program
  | loop_var : Nat → Program → Program
  | seq_execution : Program → Program → Program
open Program

notation "CLEAR X " n:68 => clear_var n
notation "INC X " n:68 => increment_var n
notation "LOOP X " n " DO " ls " END" => loop_var n ls
notation "X " i " += X " j:68 => LOOP X j DO INC X i END

instance : Append Program where
  append p p' := seq_execution p p'

example : Program := CLEAR X 0
def example_1 : Program :=
  LOOP X 1 DO
    INC X 0
  END ++
  LOOP X 2 DO
    INC X 0
  END

abbrev VarState := List Nat

def value_at (xs : VarState) (k : Nat) : Nat := xs.getD k 0

example : value_at [3, 1, 5] 2 = 5 := rfl
example : value_at [3, 1, 5] 7 = 0 := rfl

def clear_value (xs : VarState) (k : Nat) : VarState := xs.set k 0

example : clear_value [3, 1, 5] 2 = [3, 1, 0] := rfl

def inc_value : VarState → Nat → VarState
  | [],      0     => [1]
  | [],      n + 1 => 0 :: inc_value [] n
  | x :: xs, 0     => (x + 1) :: xs
  | x :: xs, n + 1 => x :: inc_value xs n

example : inc_value [3, 1, 5] 2 = [3, 1, 6] := by rfl

def init_state (v : VectNat n) : VarState := 0 :: v.toList

mutual
  def execution_from_state (xs : VarState) (p : Program) : VarState := match p with
    | clear_var n => clear_value xs n
    | increment_var n => inc_value xs n
    | loop_var n p => loop_n_times (value_at xs n) xs p
    | seq_execution p p' => execution_from_state (execution_from_state xs p) p'

  def loop_n_times : Nat → VarState → Program → VarState
    | 0, xs, _ => xs
    | n + 1, xs, p => loop_n_times n (execution_from_state xs p) p
end

def nary_program_function (p : Program) (n : Nat) (v : VectNat n) : Nat :=
  value_at (execution_from_state (init_state v) p) 0

notation "⟦ " p " ⟧^(" n ") " => nary_program_function p n

example : ⟦ example_1 ⟧^(2) ⟨[23, 4], rfl⟩ = 27 := by
  simp [nary_program_function, init_state, example_1, execution_from_state, loop_n_times, value_at, inc_value, clear_value, HAppend.hAppend, Append.append]

def loop_computable (f : VectNat n → Nat) : Prop :=
  ∃ p : Program, ⟦ p ⟧^(n) = f

def highest_var : Program → Nat
  | clear_var n => n
  | increment_var n => n
  | loop_var n p => max n (highest_var p)
  | seq_execution p p' => max (highest_var p) (highest_var p')

abbrev List.zeros (n : Nat) : List Nat := List.replicate n 0

abbrev cleanly_computes (p : Program) (f : VectNat n → Nat) : Prop :=
  ∀ v : VectNat n,
    execution_from_state (init_state v ++ List.zeros (highest_var p - n)) p
    =
    f v :: v.toList ++ List.zeros (highest_var p - n)

-- /- A function is loop computable cleanly if it does not modify the initial state,. -/
def loop_computable_cleanly (f : VectNat n → Nat) : Prop :=
  ∃ p : Program, cleanly_computes p f

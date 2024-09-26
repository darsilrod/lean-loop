/-
Copyright: TODO
Authors: Darío Silva Rodríguez
-/

import Mathlib.Data.Vector.Defs
import Mathlib.Data.List.Basic

/-!
# The Loop programming language

The goal of this file is to formally define the semantics of the Loop
programming language, define what Loop-computable functions are, and prove that
Loop-computable is the same as primitive recursive.
-/

namespace Loop


inductive Program where
  | clear_var : Nat → Program
  | increment_var : Nat → Program
  | loop_var : Nat → Program → Program
  | seq_execution : Program → Program → Program
open Program

notation "CLEAR X " n:68 => clear_var n
notation "INC X " n:68 => increment_var n
notation "LOOP X " n " DO " ls " END" => loop_var n ls

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
-- example : inc_value [3, 1, 5] 4 = [3, 1, 5, 0, 1] := by rfl

def init_state (v : Mathlib.Vector Nat n) : VarState := 0 :: v.toList

def execution_from_state (xs : VarState) (p : Program) : VarState :=
  let rec loop_n_times : Nat → VarState → Program → VarState
  | 0, xs, _ => xs
  | n + 1, xs, p => loop_n_times n (execution_from_state xs p) p
  match p with
  | clear_var n => clear_value xs n
  | increment_var n => inc_value xs n
  | loop_var n p => loop_n_times (value_at xs n) xs p
  | seq_execution p p' => execution_from_state (execution_from_state xs p) p'
open execution_from_state

def nary_program_function (p : Program) (n : Nat) (v : Mathlib.Vector Nat n) : Nat :=
  value_at (execution_from_state (init_state v) p) 0

notation "⟦ " p " ⟧^(" n ") " => nary_program_function p n

example : ⟦ example_1 ⟧^(2) ⟨[23, 4], rfl⟩ = 27 := by
  simp [nary_program_function, init_state, example_1, execution_from_state, loop_n_times, value_at, inc_value, clear_value, HAppend.hAppend, Append.append]

def loop_computable (f : Mathlib.Vector Nat n → Nat) : Prop :=
  ∃ p : Program, ⟦ p ⟧^(n) = f

-- -- -------
def highest_var : Program → Nat
  | clear_var n => n
  | increment_var n => n
  | loop_var n p => max n (highest_var p)
  | seq_execution p p' => max (highest_var p) (highest_var p')

abbrev List.zeros (n : Nat) : List Nat := List.replicate n 0

-- /- A function is loop computable cleanly if it does not modify the initial state,. -/
def loop_computable_cleanly (f : Mathlib.Vector Nat n → Nat) : Prop :=
  ∃ p : Program, ∀ v : Mathlib.Vector Nat n,
    execution_from_state (init_state v ++ List.zeros (highest_var p - n)) p
    =
    f v :: v.toList ++ List.zeros (highest_var p - n)

theorem value_at_nil : value_at [] n = 0 := rfl
theorem value_at_cons_zero : value_at (x :: xs) 0 = x := rfl
theorem value_at_cons_succ : value_at (x :: xs) (n + 1) = value_at xs n := rfl

theorem clear_value_nil : clear_value [] n = [] := rfl
theorem clear_value_cons_zero : clear_value (x :: xs) 0 = 0 :: xs := rfl
theorem clear_value_cons_succ : clear_value (x :: xs) (n + 1) = x :: clear_value xs n := rfl

theorem inc_value_nil_zero : inc_value [] 0 = [1] := rfl
theorem inc_value_nil_succ : inc_value [] (n + 1) = 0 :: inc_value [] n := rfl
theorem inc_value_cons_zero : inc_value (x :: xs) 0 = (x + 1) :: xs := rfl
theorem inc_value_cons_succ : inc_value (x :: xs) (n + 1) = x :: inc_value xs n := rfl


theorem value_at_zeros_is_zero (n k : Nat) : value_at (List.zeros n) k = 0 := by
  revert n
  induction k
  case zero =>
    intro n
    cases n <;> simp [value_at]
  case succ ih =>
    intro n
    cases n
    · simp [value_at]
    · simp [List.replicate, value_at_cons_succ, ih]


theorem append_zeros_does_not_change_value_at (xs : VarState) (n k : Nat) :
    value_at xs k = value_at (xs ++ List.zeros n) k := by
  revert k
  induction xs
  case nil => simp [value_at_nil, value_at_zeros_is_zero]
  case cons head tail tail_ih =>
    intro k
    cases k
    all_goals simp [value_at_cons_zero, value_at_cons_succ, tail_ih]

theorem clear_value_clears_value (xs : VarState) :
    value_at (clear_value xs n) k = if (n = k) then 0 else value_at xs k := by
  revert n k
  induction xs
  case nil =>
    simp [clear_value_nil, value_at_nil]
  case cons x xs xs_ih =>
    intro n k
    cases n
    · cases k <;> simp [clear_value, value_at]
    · cases k
      · simp [clear_value, value_at]
      · simp [value_at_cons_succ]
        exact xs_ih

theorem inc_value_increments_value (xs : VarState) :
    value_at (inc_value xs n) k = if (n = k) then value_at xs k + 1 else value_at xs k := by
  revert n k
  induction xs
  case nil =>
    intro n
    induction n
    case zero =>
      simp [inc_value_nil_zero, value_at_nil]
      intro k
      cases k <;> simp [value_at]
    case succ n n_ih =>
      simp [inc_value, value_at_nil]
      intro k
      induction k

      case zero =>
        simp [value_at_cons_zero]
      case succ k k_ih =>
        simp [value_at_cons_succ]
        simp [value_at_nil] at n_ih
        exact n_ih

  case cons x xs xs_ih =>
    intro n
    cases n
    · simp [inc_value_cons_zero, value_at_cons_succ]
      intro k
      cases k <;> simp [value_at]
    · simp [inc_value_cons_succ]
      intro k
      cases k <;> simp [value_at_cons_zero, value_at_cons_succ, xs_ih]


theorem same_values_same_execution (p : Program) (xs ys : VarState) :
    (∀ k : Nat, value_at xs k = value_at ys k) → ∀ k : Nat, value_at (execution_from_state xs p) k = value_at (execution_from_state ys p) k := by
  revert xs ys
  induction p
  case clear_var n =>
    intro xs ys h
    simp [execution_from_state, clear_value_clears_value, h]
  case increment_var n =>
    intro xs ys h
    simp [execution_from_state, inc_value_increments_value, h]
  case loop_var n inner inner_ih =>
    intro xs ys h
    simp [execution_from_state, h]
    generalize value_at ys n = x
    revert xs ys
    induction x
    case zero =>
      intro xs ys h
      simp [loop_n_times, h]
    case succ x x_ih =>
      intro xs ys h
      simp [loop_n_times]
      apply x_ih (execution_from_state xs inner) (execution_from_state ys inner)
      exact inner_ih xs ys h
  case seq_execution p p' p_ih p'_ih =>
    intro xs ys h
    simp [execution_from_state]
    apply p'_ih
    apply p_ih
    exact h

theorem append_zeros_does_not_change_execution (n k : Nat) :
    value_at (execution_from_state (xs ++ List.zeros n) p) k = value_at (execution_from_state xs p) k := by
  have := append_zeros_does_not_change_value_at xs n
  have := same_values_same_execution p xs (xs ++ List.zeros n) this k
  exact this.symm

theorem loop_computable_cleanly_is_loop_computable : loop_computable_cleanly f → loop_computable f := by
  rename_i n
  intro ⟨p, h⟩
  exists p
  apply funext
  intro v
  let dif := highest_var p - n
  exact
    calc
      ⟦ p ⟧^(n) v = value_at (execution_from_state (init_state v) p) 0 := by rw [nary_program_function]
                _ = value_at (execution_from_state (init_state v ++ List.zeros dif) p) 0 := by rw [append_zeros_does_not_change_execution ]
                _ = value_at (f v :: v.toList ++ List.zeros dif) 0 := by rw [h v]
                _ = f v := by rfl

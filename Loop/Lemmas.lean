/-
Copyright: TODO
Authors: Darío Silva Rodríguez
-/

import Mathlib.Data.Vector.Defs
import Mathlib.Data.Vector.Basic
import Mathlib.Computability.Primrec
import Loop.Defs

namespace Loop
open Program

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

theorem concat_is_seq_execution {p p' : Program} : p ++ p' = seq_execution p p' := by rfl

theorem zeros_succ : List.zeros (n + 1) = 0 :: List.zeros n := by
  simp [List.zeros, List.replicate]

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
    · simp [zeros_succ, value_at_cons_succ, ih]

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
      cases k
      · simp [value_at_cons_zero]
      · simp [value_at_cons_succ]
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

theorem loop_inc_adds_value :
    execution_from_state (x :: xs) (LOOP X n DO INC X 0 END) = (x + value_at (x :: xs) n) :: xs := by
  simp [execution_from_state]
  generalize value_at (x :: xs) n = k
  revert x
  induction k
  case zero =>
    simp [loop_n_times]
  case succ k k_ih =>
    simp_arith [loop_n_times, execution_from_state, inc_value, k_ih]

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

theorem clear_value_clears_succ_largest_index (xs : VarState) (l_h : xs.length ≥ k + 1) :
    clear_value (xs ++ ys) k = (clear_value xs k) ++ ys := by
  revert k
  induction xs
  case nil =>
    intro k h
    absurd h
    exact Nat.not_succ_le_zero k
  case cons x xs xs_ih =>
    intro k
    cases k
    case zero =>
      simp [clear_value]
    case succ k =>
      simp [clear_value_cons_succ]
      exact xs_ih

theorem inc_value_increments_succ_largest_index (xs : VarState) (l_h : xs.length ≥ k + 1) :
    inc_value (xs ++ ys) k = (inc_value xs k) ++ ys := by
  revert k
  induction xs
  case nil =>
    intro k h
    absurd h
    exact Nat.not_succ_le_zero k
  case cons x xs xs_ih =>
      intro k
      cases k
      case zero =>
        simp [inc_value]
      case succ k =>
        simp [inc_value_cons_succ]
        exact xs_ih

theorem value_at_first_k (v : VectNat n) (n_h : n > k) :
    value_at (v.toList ++ xs) k = value_at v.toList k := by
  revert k
  induction n
  case zero =>
    intro k k_h
    absurd k_h
    have : ¬0 > k := by simp
    exact this
  case succ n n_ih =>
    let ⟨ys, ys_l⟩ := v
    simp
    cases ys
    case nil =>
      intros
      have : ¬0 ≥ 1 := by simp
      absurd this
      have : 0 ≥ 1 := by calc
        0 = n + 1 := ys_l
        _ ≥ 1 := by simp
      exact this
    case cons y ys =>
      intro k k_h
      have tail_l : ys.length = n := by
        rw [List.length] at ys_l
        exact Nat.succ_injective ys_l
      cases k
      case zero =>
        simp [value_at_cons_zero]
      case succ k =>
        simp [value_at_cons_succ]
        have : k < n := Nat.lt_of_succ_lt_succ k_h
        have := n_ih ⟨ys, tail_l⟩ this
        simp at this
        assumption

theorem execution_from_state_long_enough_preserves_length (p : Program) (v : VectNat n) (n_h : n ≥ highest_var p + 1) :
    (execution_from_state v.toList p).length = n := by
  revert n
  induction p
  case clear_var k =>
    induction k
    case zero =>
      intro n v n_h
      simp [highest_var] at n_h
      cases n
      case zero =>
        absurd n_h
        have : ¬1 ≤ 0 := by simp
        exact this
      case succ n =>
        let ⟨x :: xs, xs_l⟩ := v
        simp at xs_l
        simp [execution_from_state, clear_value, xs_l]
    case succ k k_ih =>
      intro n v n_h
      simp [highest_var] at n_h
      cases n
      case zero =>
        have : 1 ≤ 0 := by
          have : 1 ≤ k + 1 + 1 := by simp
          exact Nat.le_trans this n_h
        absurd this
        have : ¬1 ≤ 0 := by simp
        exact this
      case succ n =>
        simp at n_h
        let ⟨x :: xs, xs_l⟩ := v
        simp [execution_from_state, clear_value_cons_succ]
        simp at xs_l
        have := k_ih ⟨xs, xs_l⟩ n_h
        simp [execution_from_state] at this
        assumption

  case increment_var k =>
    induction k
    case zero =>
      intro n v n_h
      simp [highest_var] at n_h
      cases n
      case zero =>
        absurd n_h
        have : ¬1 ≤ 0 := by simp
        exact this
      case succ n =>
        let ⟨x :: xs, xs_l⟩ := v
        simp at xs_l
        simp [execution_from_state, inc_value, xs_l]
    case succ k k_ih =>
      intro n v n_h
      simp [highest_var] at n_h
      cases n
      case zero =>
        have : 1 ≤ 0 := by
          have : 1 ≤ k + 1 + 1 := by simp
          exact Nat.le_trans this n_h
        absurd this
        have : ¬1 ≤ 0 := by simp
        exact this
      case succ n =>
        simp at n_h
        let ⟨x :: xs, xs_l⟩ := v
        simp [execution_from_state, inc_value_cons_succ]
        simp at xs_l
        have := k_ih ⟨xs, xs_l⟩ n_h
        simp [execution_from_state] at this
        assumption

  case loop_var k inner inner_ih =>
    simp [execution_from_state]
    intro n v
    generalize value_at v.toList k = m
    revert n v
    induction m
    case zero =>
      simp [loop_n_times]
    case succ m m_ih =>
      intro n v n_h
      simp [loop_n_times]
      let ys := execution_from_state v.toList inner
      simp [highest_var] at n_h
      have ineq : highest_var inner + 1 ≤ n := by
        have : highest_var inner + 1 ≤ max k (highest_var inner) + 1 := by simp
        exact Nat.le_trans this n_h
      have := inner_ih v ineq
      let w' : VectNat n := ⟨ys, this⟩
      have : execution_from_state v.toList inner = w'.toList := rfl
      rw [this]
      exact m_ih w' n_h

  case seq_execution p p' p_ih p'_ih =>
    intro n v n_h
    let ys := execution_from_state v.toList p
    have : n ≥ highest_var p + 1 := by
      rw [highest_var] at n_h
      have : max (highest_var p) (highest_var p') + 1 ≥ highest_var p + 1 := by simp
      exact Nat.le_trans this n_h
    have := p_ih v this
    let w' : VectNat n := ⟨ys, this⟩
    simp [execution_from_state]
    have : execution_from_state v.toList p = w'.toList := rfl
    rw [this]
    have : n ≥ highest_var p' + 1 := by
      rw [highest_var] at n_h
      have : max (highest_var p) (highest_var p') + 1 ≥ highest_var p' + 1 := by simp
      exact Nat.le_trans this n_h
    exact p'_ih w' this

theorem execution_from_state_ge_highest_append (v : VectNat n) (n_h : n ≥ highest_var p) :
    execution_from_state (init_state v ++ xs) p = (execution_from_state (init_state v) p) ++ xs := by
  suffices g : (w : VectNat (n + 1)) →  execution_from_state (w.toList ++ xs) p = (execution_from_state w.toList p) ++ xs from by
    let w : VectNat (n + 1) := ⟨0 :: v.toList, by simp⟩
    exact g w
  revert n
  induction p
  case clear_var k =>
    intro n _ n_h w
    simp [execution_from_state]
    have : w.toList.length ≥ k + 1 := by
      have : k ≤ n := by  simp [highest_var] at n_h; assumption
      simp_arith [this]
    exact clear_value_clears_succ_largest_index w.toList this
  case increment_var k =>
    intro n _ n_h w
    simp [execution_from_state]
    have : w.toList.length ≥ k + 1 := by
      have : k ≤ n := by simp [highest_var] at n_h; assumption
      simp_arith [this]
    exact inc_value_increments_succ_largest_index w.toList this
  case loop_var k inner inner_ih =>
    intro n _ n_h w
    simp [execution_from_state]
    have : value_at (w.toList ++ xs) k = value_at w.toList k := by
      have : n ≥ k := by
        simp [highest_var] at n_h
        exact n_h.left
      have : n + 1 > k := by simp_arith [this]
      exact value_at_first_k w this
    rw [this]
    generalize value_at w.toList k = m
    revert w n
    induction m
    case zero =>
      intros
      simp [loop_n_times]
    case succ m m_ih =>
      intro n v n_h w _
      simp [loop_n_times]
      have : n ≥ highest_var inner := by
        simp [highest_var] at n_h
        exact n_h.right
      simp[inner_ih v this w]
      let ys := execution_from_state w.toList inner
      have : ys.length = n + 1 := by
        have : n + 1 ≥ highest_var inner + 1 := by simp_arith [this]
        simp [execution_from_state_long_enough_preserves_length inner w this]
      let w' : VectNat (n + 1) := ⟨ys, this⟩
      have : execution_from_state w.toList inner = w'.toList := rfl
      rw [this]
      have : value_at (w'.toList ++ xs) k = value_at w'.toList k := by
        have : n ≥ k := by
          simp [highest_var] at n_h
          exact n_h.left
        have : n + 1 > k := by simp_arith [this]
        exact value_at_first_k w' this
      exact m_ih v n_h w' this
  case seq_execution p p' p_ih p'_ih =>
    intro n v n_h w
    simp [execution_from_state]
    have : n ≥ highest_var p := by
      simp [highest_var] at n_h
      exact n_h.left
    rw [p_ih v this]
    let ys := execution_from_state w.toList p
    have : ys.length = n + 1 := by
      have : n + 1 ≥ highest_var p + 1 := by simp [this]
      simp [execution_from_state_long_enough_preserves_length p w this]
    let w' : VectNat (n + 1) := ⟨ys, this⟩
    have : execution_from_state w.toList p = w'.toList := rfl
    rw [this]
    have : n ≥ highest_var p' := by
      simp [highest_var] at n_h
      exact n_h.right
    exact p'_ih v this w'

theorem execution_from_state_append_xs (v : VectNat n) :
    execution_from_state (init_state v ++ List.zeros (highest_var p - n) ++ xs) p
    = (execution_from_state (init_state v ++ List.zeros (highest_var p - n)) p) ++ xs := by
  rw [init_state]
  let ys := v.toList ++ List.zeros (highest_var p - n)
  let m := ys.length
  have m_h : m ≥ highest_var p := by
    simp [m, ys]
    rw [Nat.add_comm, Nat.sub_add_eq_max]
    exact Nat.le_max_left (highest_var p) n
  let w : VectNat m := ⟨ys, rfl⟩
  have : 0 :: w.toList = 0 :: v.toList ++ List.zeros (highest_var p - n) := rfl
  rw [←this, ←init_state, execution_from_state_ge_highest_append w m_h]

theorem cleanly_computable_append_xs {f : VectNat n → Nat} (h_p : cleanly_computes p f) :
    ∀ xs : VarState, ∀ v : VectNat n,
      execution_from_state (init_state v ++ List.zeros (highest_var p - n) ++ xs) p
      =
      (f v) :: v.toList ++ List.zeros (highest_var p - n) ++ xs := by
  intros
  rw [execution_from_state_append_xs, h_p]

theorem append_zeros_addition (a b c : Nat) (e : a + b = c) :
    List.zeros a ++ List.zeros b = List.zeros c := by
  simp [e]

theorem cleanly_computable_append_zeros_append_xs {f : VectNat n → Nat} {k : Nat} (h_p : cleanly_computes p f) :
    ∀ xs : VarState, ∀ v : VectNat n,
    k ≥ highest_var p - n →
      execution_from_state (init_state v ++ List.zeros k ++ xs) p
      =
      f v :: v.toList ++ List.zeros k ++ xs := by
  intro xs v k_h
  have : (highest_var p - n) + (k - (highest_var p - n)) = k := by
    have := Nat.sub_add_eq_max k (highest_var p - n)
    rw [Nat.add_comm, Nat.max_eq_left k_h] at this
    assumption
  let m := highest_var p - n

  exact calc
    execution_from_state (init_state v ++ List.zeros k ++ xs) p
    _ =
    execution_from_state (init_state v ++ (List.zeros m ++ List.zeros (k - m)) ++ xs) p := by rw [append_zeros_addition _ _ _ this]
    _  =
    execution_from_state (init_state v ++ List.zeros m ++ (List.zeros (k - m) ++ xs)) p := by repeat rw [List.append_assoc]
    _ =
    f v :: v.toList ++ List.zeros m ++ (List.zeros (k - m) ++ xs) := by exact cleanly_computable_append_xs h_p _ v
        _ =
    f v :: v.toList ++ (List.zeros m ++ List.zeros (k - m)) ++ xs := by repeat rw [List.append_assoc]
    _ =
    f v :: v.toList ++ List.zeros k ++ xs := by rw [append_zeros_addition _ _ _ this]

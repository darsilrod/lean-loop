/-
Copyright: TODO
Authors: Darío Silva Rodríguez
-/

import Mathlib.Data.Vector.Defs
import Mathlib.Data.Vector.Basic
import Mathlib.Data.List.Basic
import Mathlib.Computability.Primrec

/-!
# The Loop programming language

The goal of this file is to formally define the semantics of the Loop
programming language, define what Loop-computable functions are, and prove that
Loop-computable is the same as primitive recursive.
-/

abbrev VectNat := Mathlib.Vector Nat

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

def init_state (v : VectNat n) : VarState := 0 :: v.toList

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

def nary_program_function (p : Program) (n : Nat) (v : VectNat n) : Nat :=
  value_at (execution_from_state (init_state v) p) 0

notation "⟦ " p " ⟧^(" n ") " => nary_program_function p n

example : ⟦ example_1 ⟧^(2) ⟨[23, 4], rfl⟩ = 27 := by
  simp [nary_program_function, init_state, example_1, execution_from_state, loop_n_times, value_at, inc_value, clear_value, HAppend.hAppend, Append.append]

def loop_computable (f : VectNat n → Nat) : Prop :=
  ∃ p : Program, ⟦ p ⟧^(n) = f

-- -- -------
def highest_var : Program → Nat
  | clear_var n => n
  | increment_var n => n
  | loop_var n p => max n (highest_var p)
  | seq_execution p p' => max (highest_var p) (highest_var p')

abbrev List.zeros (n : Nat) : List Nat := List.replicate n 0

theorem zeros_succ : List.zeros (n + 1) = 0 :: List.zeros n := by
  simp [List.zeros, List.replicate]

abbrev cleanly_computes (p : Program) (f : VectNat n → Nat) : Prop :=
  ∀ v : VectNat n,
    execution_from_state (init_state v ++ List.zeros (highest_var p - n)) p
    =
    f v :: v.toList ++ List.zeros (highest_var p - n)

-- /- A function is loop computable cleanly if it does not modify the initial state,. -/
def loop_computable_cleanly (f : VectNat n → Nat) : Prop :=
  ∃ p : Program, cleanly_computes p f

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

notation "X " i " += X " j:68 => LOOP X j DO INC X i END

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

---
def zero_fun_vect : VectNat 0 → Nat := fun _ => 0

theorem zero_is_loop_computable_cleanly : loop_computable_cleanly zero_fun_vect := by
  let p := CLEAR X 0
  exists p
  intro v
  simp [init_state, highest_var, p, execution_from_state, clear_value, zero_fun_vect]

def succ_fun_vect : VectNat 1 → Nat := fun v => v.head + 1

theorem succ_is_loop_computable_cleanly : loop_computable_cleanly succ_fun_vect := by
  let p₁ :=
    LOOP X 1 DO
      INC X 0
    END
  let p₂ := INC X 0

  let p := p₁ ++ p₂

  exists p
  intro v
  simp [init_state, succ_fun_vect, highest_var]
  exact calc
    execution_from_state [0, v.head] p
      =
    inc_value (execution_from_state [0, v.head] p₁) 0 := by simp [p, concat_is_seq_execution, execution_from_state, p₂]
    _ =
    inc_value [v.head, v.head] 0 := by simp [p₁, loop_inc_adds_value, value_at]
    _ = [v.head + 1, v.head] := by simp [inc_value]

theorem get_is_loop_computable_cleanly (i : Fin n) : loop_computable_cleanly (fun v => v.get i) := by
  let p :=
    LOOP X i + 1 DO
      INC X 0
    END
  exists p
  intro v
  have : i + 1 - n = 0 := by exact Nat.sub_eq_zero_iff_le.2 i.isLt
  simp [init_state, highest_var, this, p, execution_from_state,
    loop_inc_adds_value, value_at_cons_succ, value_at, Mathlib.Vector.get_eq_get]

theorem comp_is_loop_computable_cleanly (g : Fin n → VectNat m → ℕ) :
      loop_computable_cleanly f
    → (∀ i, loop_computable_cleanly (g i))
    → loop_computable_cleanly fun a => f (Mathlib.Vector.ofFn fun i => g i a) := by
  sorry

theorem prec_is_loop_computable_cleanly {f : VectNat n → Nat}
    {g : VectNat (n + 2) → Nat} : loop_computable_cleanly f
    → loop_computable_cleanly g
    → loop_computable_cleanly fun v : Mathlib.Vector ℕ (n + 1) =>
      v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail) := by
  intro ⟨p_f, f_h⟩ ⟨p_g, g_h⟩

  -- Definitions for the variables that will be used in the program
  let a := highest_var p_f
  let b := highest_var p_g
  let offset := max (n + 2) (max a b)
  let result := offset + 1
  let Z := fun j => offset + 2 + j -- from Z 0 to Z n

  -- Step 1: compute f of the last n inputs and store the result in the
  -- 'result' variable

  -- -- 1.1: Store inputs
  -- Note: defined using the recursor instead of 'let rec' construct. This
  -- allows us to expand the defintion and prove prove properties about the
  -- function
  let store_X_1_to_X_succ_n : Nat → Program := Nat.rec
    (X (Z 0) += X 1)
    fun n p_ind => p_ind ++ X (Z (n + 1)) += X (n + 2)

  let p_1_1 := store_X_1_to_X_succ_n n

  -- -- 1.2: Clear inputs
  -- TODO: check correctness
  let clear_X_j_to_X_j_plus_n (j : Nat) : Nat → Program := Nat.rec
    (CLEAR X j)
    fun n p_ind => p_ind ++ CLEAR X (j + (n + 1))

  let p_1_2 := clear_X_j_to_X_j_plus_n 1 n

  -- -- 1.3. Setup inputs and execute f
  let setup_X_j_to_X_j_plus_succ_n (j : Nat) : Nat → Program := Nat.rec
    (X j += X (Z 1))
    fun n p_ind => p_ind ++ X (j + (n + 1)) += X (Z (n + 1))

  let setup_X_1_to_X_n_and_execute_f : Nat → Program
    | 0 => p_f
    | n + 1 => setup_X_j_to_X_j_plus_succ_n 1 n ++ p_f

  let p_1_3 := setup_X_1_to_X_n_and_execute_f n

  -- -- 1.5. Store result
  let p_1_4 := X result += X 0

  -- -- 1.6. Clear X 0
  let p_1_5 := CLEAR X 0

  let p_1 := p_1_1 ++ p_1_2 ++ p_1_3 ++ p_1_4 ++ p_1_5


  -- Step 2: compute g counter number of times, for each recursive step

  -- 2.1: Setup X 2
  let p_2_1 := CLEAR X 2

  -- 2.2: Setup X 1
  let p_2_2 := CLEAR X 1 ++ X 1 += X result

  -- 2.3: Setup inputs and execute_p_g
  let setup_X_3_to_X_succ_succ_n_and_execute_g : Nat → Program
  | 0 => p_g
  | n + 1 => setup_X_j_to_X_j_plus_succ_n 3 n ++ p_g

  let p_2_3 : Program := setup_X_3_to_X_succ_succ_n_and_execute_g n

  -- 2.4: Store result
  let p_2_4 := CLEAR X result ++ X result += X 0

  -- 2.5: Clear X 0
  let p_2_5 := CLEAR X 0

  -- 2.6: Increment X 2
  let p_2_6 := INC X 2

  -- 2.7: Loop
  let loop_inner := p_2_2 ++ p_2_3 ++ p_2_4 ++ p_2_5 ++ p_2_6
  let p_2_7 := LOOP X (Z 0) DO loop_inner END

  let p_2 := p_2_1 ++ p_2_7


  -- -- Step 3: Clean up

  -- -- 3.1: Setup X 0
  let p_3_1 := X 0 += X result

  -- -- 3.2: Clear inputs
  let p_3_2 := clear_X_j_to_X_j_plus_n 1 (n + 1)

  -- -- 3.3: Setup inputs
  let p_3_3 : Program := X 1 += X (Z 0) ++ setup_X_j_to_X_j_plus_succ_n 2 n

  -- -- 3.4: Clear result
  let p_3_4 := CLEAR X result

  -- -- 3.5: Clear Z j
  let rec clear_Z_0_to_Z_n : Nat → Program
  | 0 => CLEAR X (Z 0)
  | n + 1 => clear_Z_0_to_Z_n n ++ CLEAR X (Z (n + 1))

  let p_3_5 : Program := clear_Z_0_to_Z_n n

  let p_3 := p_3_1 ++ p_3_2 ++ p_3_3 ++ p_3_4 ++ p_3_5

  -- Final program
  let p := p_1 ++ p_2 ++ p_3
  exists p

  intro v

  -- Rewriting to analyise the program more easily
  have highest_var_store (n : Nat) : highest_var (store_X_1_to_X_succ_n n) = offset + n + 2 := by
    induction n
    case zero =>
      simp [highest_var, Z]
    case succ n n_ih =>
      simp [highest_var, n_ih, Z]
      sorry

  have highest_var_clear (j : Nat) (n : Nat) : highest_var (clear_X_j_to_X_j_plus_n j n) = j + (n + 1) := by
    induction n
    case zero =>
      simp [highest_var]
      sorry
    sorry

  have highest_var_p_1 : highest_var p_1 = offset + n + 2 := by
    simp [p_1, concat_is_seq_execution, highest_var]
    sorry
  have highest_var_p_2 : highest_var p_2 = offset + 2 := by
    simp [p_2, concat_is_seq_execution, highest_var, Z]
    constructor
    · simp [result]
    · simp [p_2_3]
      sorry
  have highest_var_p_3 : highest_var p_3 = offset + n + 2 := by sorry
  have : highest_var p = offset + n + 2 := by
    simp [p, concat_is_seq_execution]
    repeat rw [highest_var]
    rw [highest_var_p_1, highest_var_p_2, highest_var_p_3]
    simp_arith
  rw [this]
  have : offset + n + 2 - (n + 1) = 1 + offset := by calc
    offset + n + 2 - (n + 1)
      = offset + ((n + 1) + 1) - (n + 1) := rfl
    _ = offset + (1 + (n + 1)) - (n + 1) := by rw [Nat.add_comm (n + 1) 1]
    _ = offset + 1 + (n + 1) - (n + 1) := by rw [Nat.add_assoc]
    _ = offset + 1 := Nat.add_sub_self_right _ _
    _ = 1 + offset := Nat.add_comm offset 1
  rw [this]
  let padding := offset - (n + 2)
  have : offset = padding + (1 + (n + 1)) := by
    simp [offset, padding]
    have : 1 + (n + 1) = n + 2 := Nat.add_comm _ _
    rw [this]
    simp [Nat.add_sub_self_right]
  rw [this]
  rw [init_state]
  have : List.zeros (1 + (padding + (1 + (n + 1)))) = 0 :: List.zeros (padding + (1 + (n + 1))) := by rw [Nat.add_comm, zeros_succ]
  rw [this, ←append_zeros_addition padding (1 + (n + 1)) (padding + (1 + (n + 1))) rfl]
  have : List.zeros (1 + (n + 1)) = 0 :: 0 :: List.zeros n := by rw [Nat.add_comm, zeros_succ, zeros_succ]
  rw [this]
  have : 0 :: v.toList ++ 0 :: (List.zeros padding ++ 0 :: 0 :: List.zeros n)
    = 0 :: v.toList ++ 0 :: List.zeros padding ++ 0 :: 0 :: List.zeros n := by simp
  repeat rw [this]


  sorry

theorem primrec_is_loop_computable_cleanly : Nat.Primrec' f → loop_computable_cleanly f := by
  intro h
  induction h
  case zero => exact zero_is_loop_computable_cleanly
  case succ => exact succ_is_loop_computable_cleanly
  case get i => exact get_is_loop_computable_cleanly i
  case comp g _ _ f_ih g_ih => exact comp_is_loop_computable_cleanly g f_ih g_ih
  case prec f_ih g_ih => exact prec_is_loop_computable_cleanly f_ih g_ih

theorem primrec_is_loop_computable {f : VectNat n → Nat} :
    Primrec f → loop_computable f := by
  intro h
  have := Nat.Primrec'.of_prim h
  have := primrec_is_loop_computable_cleanly this
  have := loop_computable_cleanly_is_loop_computable this
  assumption

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

theorem seq_execution_unfold : execution_from_state xs (seq_execution p p') = execution_from_state (execution_from_state xs p) p' := by simp [execution_from_state]

theorem zeros_succ : List.zeros (n + 1) = 0 :: List.zeros n := by
  simp [List.zeros, List.replicate]

theorem zeros_length : (List.zeros n).length = n := by
  dsimp [List.zeros]
  rw [List.length_replicate]

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

theorem execution_from_state_gt_highest_append {n : Nat} (v : VectNat (n + 1)) (n_h : n ≥ highest_var p) :
    execution_from_state (v.toList ++ xs) p = (execution_from_state v.toList p) ++ xs := by
  revert n
  induction p
  case clear_var k =>
    intro n v n_h
    simp [execution_from_state]
    have : v.toList.length ≥ k + 1 := by
      have : k ≤ n := by simp [highest_var] at n_h; assumption
      simp_arith [this]
    exact clear_value_clears_succ_largest_index v.toList this
    -- have := clear_value_clears_succ_largest_index v.toList
  case increment_var k =>
    intro n v n_h
    simp [execution_from_state]
    have : v.toList.length ≥ k + 1 := by
      have : k ≤ n := by simp [highest_var] at n_h; assumption
      simp_arith [this]
    exact inc_value_increments_succ_largest_index v.toList this
  case loop_var k inner inner_ih =>
    intro n v n_h
    simp [execution_from_state]
    have : value_at (v.toList ++ xs) k = value_at v.toList k := by
      have : n ≥ k := by
        simp [highest_var] at n_h
        exact n_h.left
      have : n + 1 > k := by simp_arith [this]
      exact value_at_first_k v this
    rw [this]
    generalize value_at v.toList k = m
    revert v n
    induction m
    case zero =>
      intros
      simp [loop_n_times]
    case succ m m_ih =>
      intro n v n_h _
      simp [loop_n_times]
      have : n ≥ highest_var inner := by
        simp [highest_var] at n_h
        exact n_h.right
      simp[inner_ih v this]
      let ys := execution_from_state v.toList inner
      have : ys.length = n + 1 := by
        have : n + 1 ≥ highest_var inner + 1 := by simp_arith [this]
        simp [execution_from_state_long_enough_preserves_length inner v this]
      let v' : VectNat (n + 1) := ⟨ys, this⟩
      have : execution_from_state v.toList inner = v'.toList := rfl
      rw [this]
      have : value_at (v'.toList ++ xs) k = value_at v'.toList k := by
        have : n ≥ k := by
          simp [highest_var] at n_h
          exact n_h.left
        have : n + 1 > k := by simp_arith [this]
        exact value_at_first_k v' this
      exact m_ih v' n_h this

  case seq_execution p p' p_ih p'_ih =>
    intro n v n_h
    simp [execution_from_state]
    have : n ≥ highest_var p := by
      simp [highest_var] at n_h
      exact n_h.left
    rw [p_ih v this]
    let ys := execution_from_state v.toList p
    have : ys.length = n + 1 := by
      have : n + 1 ≥ highest_var p + 1 := by simp [this]
      simp [execution_from_state_long_enough_preserves_length p v this]
    let v' : VectNat (n + 1) := ⟨ys, this⟩
    have : execution_from_state v.toList p = v'.toList := rfl
    rw [this]
    have : n ≥ highest_var p' := by
      simp [highest_var] at n_h
      exact n_h.right
    exact p'_ih v' this

theorem execution_from_init_state_ge_highest_append (v : VectNat n) (n_h : n ≥ highest_var p) :
    execution_from_state (init_state v ++ xs) p = (execution_from_state (init_state v) p) ++ xs := by
  apply execution_from_state_gt_highest_append (0 ::ᵥ v) n_h

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
  rw [←this, ←init_state, execution_from_init_state_ge_highest_append w m_h]

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

theorem highest_var_concat : highest_var (p1 ++ p2) = max (highest_var p1) (highest_var p2) := by simp [highest_var]

theorem loop_n_times_loop : loop_n_times (n + 1) xs p = execution_from_state (loop_n_times n xs p) p := by
  revert xs
  induction n
  case zero =>
    simp [loop_n_times]
  case succ n n_ih =>
    intro xs
    have : loop_n_times ((n + 1) + 1) xs p = loop_n_times (n + 1) (execution_from_state xs p) p := by simp [loop_n_times]
    rw [this, n_ih, ←loop_n_times]

theorem value_at_n : (xs.length = n) →
    value_at (xs ++ y :: ys) n = y := by
  revert xs
  induction n
  case zero =>
    simp [value_at_cons_zero]
  case succ n n_ih =>
    intro xs xs_l
    let (x :: xs) := xs
    simp at xs_l
    have : x :: xs ++ y :: ys = x :: (xs ++ y :: ys) := by simp
    rw [this, value_at_cons_succ, n_ih xs_l]

theorem clear_value_at_n : (xs.length = n) →
    clear_value (xs ++ y :: ys) n = xs ++ 0 :: ys := by
  revert xs
  induction n
  case zero =>
    simp [clear_value]
  case succ n n_ih =>
    intro xs xs_l
    let (x :: xs) := xs
    simp at xs_l
    rw [List.cons_append, clear_value_cons_succ, n_ih xs_l, List.cons_append]

theorem inc_value_at_n : (xs.length = n) →
    inc_value (xs ++ y :: ys) n = xs ++ (y + 1) :: ys := by
  revert xs
  induction n
  case zero =>
    simp [inc_value]
  case succ n n_ih =>
    intro xs xs_l
    let (x :: xs) := xs
    simp at xs_l
    rw [List.cons_append, inc_value_cons_succ, n_ih xs_l, List.cons_append]

theorem inc_X_i_X_j_adds_value : (xs.length = n) →
    execution_from_state (xs ++ y :: ys) (X n += X j)
      = xs ++ [y + value_at (xs ++ y :: ys) j] ++ ys := by
  intro xs_l
  simp [inc_X_i_X_j, execution_from_state]
  let k := value_at (xs ++ y :: ys) j
  have : value_at (xs ++ y :: ys) j = k := rfl
  rewrite [this]
  induction k
  case zero =>
    simp [loop_n_times]
  case succ k k_ih =>
    rewrite [loop_n_times_loop, k_ih]
    simp [execution_from_state]
    rw [inc_value_at_n xs_l, Nat.add_assoc y k 1]

theorem nested_max_lemma {a b : Nat} :
    max (max a b) (max (a + 1) (b + 1)) = max (a + 1) (b + 1) := by
  cases Nat.decLe a b
  case isTrue h =>
    repeat rw [Nat.max_def]
    simp [h]
  case isFalse h =>
    repeat rw [Nat.max_def]
    simp [h]

theorem List.take_n_concat_last_eq (xs : List α) (xs_l : xs.length = n + 1) :
    xs = xs.take n ++ [xs.getLast (List.ne_nil_of_length_eq_add_one xs_l)] := by
  revert xs
  induction n
  case zero =>
    intro xs xs_l
    let [x] := xs
    dsimp [List.take]
  case succ n n_ih =>
    intro xs xs_l
    let (x :: xs) := xs
    simp_arith [List.length] at xs_l
    dsimp [List.take]
    rewrite [List.cons_inj_right, List.getLast_cons (List.ne_nil_of_length_eq_add_one xs_l)]
    exact n_ih xs xs_l

theorem List.zeros_concat : List.zeros (n + 1) = List.zeros n ++ [0] := by
  have := take_n_concat_last_eq (zeros (n + 1)) zeros_length
  simp at this
  rewrite [←List.zeros] at this
  assumption

theorem highest_var_store : highest_var (store_X_1_to_X_succ_n idx n) = max (n + 1) (idx + n) := by
  induction n
  case zero =>
    simp [store_X_1_to_X_succ_n, highest_var]
  case succ n n_ih =>
    simp [store_X_1_to_X_succ_n, highest_var, n_ih]
    rw [Nat.add_assoc n 1 1, ←Nat.add_assoc idx n 1]

theorem highest_var_clear : highest_var (clear_X_j_to_X_n_plus_j j n) = n + j := by
  induction n
  case zero =>
    simp [clear_X_j_to_X_n_plus_j, highest_var]
  case succ n n_ih =>
    simp [clear_X_j_to_X_n_plus_j, highest_var, n_ih]

theorem highest_var_setup : highest_var (setup_X_j_to_X_n_plus_j idx j n) = max (n + j) (idx + n + 1) := by
  induction n
  case zero =>
    simp [setup_X_j_to_X_n_plus_j, highest_var]
    rw [Nat.max_comm]
  case succ n n_ih =>
    simp [setup_X_j_to_X_n_plus_j, highest_var, n_ih]
    have : n + 1 + j = n + j + 1 := by rw [Nat.add_assoc, Nat.add_comm 1, Nat.add_assoc]
    rw [this]
    have : idx + (n + 1) + 1 = idx + n + 2 := by repeat rw [Nat.add_assoc]
    rw [this]
    have : idx + n + 2 = (idx + n + 1) + 1 := by repeat rw [Nat.add_assoc]
    rw [this]
    generalize n + j = a
    generalize idx + n + 1 = b
    rw [Nat.max_comm (b + 1)]
    exact nested_max_lemma

theorem highest_var_clear_Z (n : Nat) : highest_var (clear_Z_0_to_Z_n idx n) = idx + n:= by
  induction n
  case zero =>
    simp [highest_var]
  case succ n n_ih =>
    simp  [highest_var, n_ih]
    exact Nat.add_assoc _ _ _

theorem clear_Z_succ : execution_from_state (x :: xs) (clear_Z_0_to_Z_n (k + 1) n)
    = x :: execution_from_state xs (clear_Z_0_to_Z_n k n) := by
  induction n
  case zero =>
    dsimp [clear_Z_0_to_Z_n]
    simp [execution_from_state]
    rw [clear_value_cons_succ]
  case succ n n_ih =>
    dsimp [clear_Z_0_to_Z_n, concat_is_seq_execution]
    simp [execution_from_state]
    rewrite [n_ih]
    rewrite [clear_value_cons_succ]
    rw [Nat.add_assoc, Nat.add_comm 1 n, Nat.add_assoc]

theorem clear_Z_lemma (v : VectNat (n + 1)) : (xs.length = k) →
    execution_from_state (xs ++ v.toList) (clear_Z_0_to_Z_n k n)
      = xs ++ List.zeros (n + 1) := by
  revert xs
  induction k
  case zero =>
    intro xs xs_l
    have : xs = [] := List.eq_nil_of_length_eq_zero xs_l
    rewrite [this]
    simp
    revert v
    induction n
    case zero =>
      intros
      simp [clear_Z_0_to_Z_n, execution_from_state, clear_value]
    case succ n n_ih =>
      intro v
      dsimp [clear_Z_0_to_Z_n, concat_is_seq_execution]
      simp [execution_from_state]
      let xs := v.toList.take (n + 1)
      have := List.ne_nil_of_length_eq_add_one v.length_val
      let t := v.toList.getLast this
      have v_list : v.toList = xs ++ [t] := List.take_n_concat_last_eq _ (by simp [this])
      have xs_l : xs.length = n + 1 := by
        have := congrArg (List.length) v_list
        simp at this
        exact this.symm
      rewrite [v_list]
      have : highest_var (clear_Z_0_to_Z_n 0 n) = n := by simp_arith [highest_var_clear_Z]
      have := @execution_from_state_gt_highest_append (clear_Z_0_to_Z_n 0 n) [t] n
        ⟨xs, xs_l⟩ (by simp_arith [this])
      dsimp at this
      rewrite [this]
      have := n_ih ⟨xs, xs_l⟩
      dsimp at this
      rewrite [this]
      have : (List.zeros (n + 1)).length = n + 1 := by simp
      rewrite [clear_value_at_n this]
      rw [←List.zeros_concat]
  case succ k k_ih =>
    intro xs xs_l
    let w : VectNat (k + 1) := ⟨xs, xs_l⟩
    have : xs = w.toList := rfl
    rewrite [this]
    let ⟨x :: xs, xs_l⟩ := w
    dsimp
    rewrite [clear_Z_succ]
    simp at xs_l
    rw [k_ih xs_l]

theorem clear_X_succ : execution_from_state (x :: xs) (clear_X_j_to_X_n_plus_j (j + 1) n)
    = x :: execution_from_state xs (clear_X_j_to_X_n_plus_j j n) := by
  induction n
  case zero =>
    simp [clear_X_j_to_X_n_plus_j, execution_from_state]
    rw [clear_value_cons_succ]
  case succ n n_ih =>
    simp [clear_X_j_to_X_n_plus_j, concat_is_seq_execution, execution_from_state]
    rw [n_ih, ←Nat.add_assoc, clear_value_cons_succ]

theorem clear_X_lemma (v : VectNat (n + 1)) : execution_from_state v.toList (clear_X_j_to_X_n_plus_j 0 n) = List.zeros (n + 1) := by
  induction n
  case zero =>
    simp [clear_X_j_to_X_n_plus_j, execution_from_state, clear_value]
  case succ n n_ih =>
    simp [clear_X_j_to_X_n_plus_j, concat_is_seq_execution, execution_from_state]
    let xs := v.toList.take (n + 1)
    have := List.ne_nil_of_length_eq_add_one v.length_val
    let t := v.toList.getLast this
    have v_list : v.toList = xs ++ [t] := List.take_n_concat_last_eq _ (by simp [this])
    have xs_l : xs.length = n + 1 := by
      have := congrArg (List.length) v_list
      simp at this
      exact this.symm
    rewrite [v_list]
    have : highest_var (clear_X_j_to_X_n_plus_j 0 n) ≤ n := by
      have : highest_var (clear_X_j_to_X_n_plus_j 0 n) = n := highest_var_clear
      rewrite [this]
      exact Nat.le_refl _
    have := @execution_from_state_gt_highest_append (clear_X_j_to_X_n_plus_j 0 n) [t] n
        ⟨xs, xs_l⟩ this
    simp at this
    rewrite [this]
    have := n_ih ⟨xs, xs_l⟩
    simp at this
    rewrite [this, clear_value_at_n]
    rw [←List.zeros_concat]
    simp

theorem clear_X_1_lemma (v : VectNat (n + 1)) : execution_from_state (0 :: v.toList) (clear_X_j_to_X_n_plus_j 1 n) = 0 :: List.zeros (n + 1) := by
  rw [clear_X_succ, clear_X_lemma]

theorem lemma_store : ∀ c n : Nat, ∀ w : VectNat c, ∀ v : VectNat (n + 1),
    execution_from_state (0 :: v.toList ++  w.toList ++ List.zeros (n + 1)) (store_X_1_to_X_succ_n (n + c + 2) n)
      = 0 :: v.toList ++  w.toList ++ v.toList := by
  intro c n
  revert c
  induction n
  case zero =>
    intro c w v
    let ⟨[x], xs_l⟩ := v
    simp [Mathlib.Vector.head, store_X_1_to_X_succ_n, execution_from_state]
    let ys := 0 :: x :: w.toList
    have : 0 :: x :: (Mathlib.Vector.toList w ++ [0]) = 0 :: x :: w.toList ++ [0] := by simp
    rewrite [this]
    have : ys.length = c + 2 := by
      dsimp [ys]
      let ⟨ws, ws_l⟩ := w
      dsimp
      rw [ws_l]
    rewrite [inc_X_i_X_j_adds_value this]
    simp [ys, value_at]
  case succ n n_ih =>
    intro c w v
    let xs := v.toList.take (n + 1)
    have := List.ne_nil_of_length_eq_add_one v.length_val
    let t := v.toList.getLast this
    have v_list : v.toList = xs ++ [t] := List.take_n_concat_last_eq _ (by simp [this])
    rewrite [v_list]
    have xs_l : xs.length = n + 1 := by
      have : (xs ++ [t]).length = v.toList.length := by rw [v_list]
      simp [List.length_concat] at this
      assumption
    have : 0 :: (xs ++ [t]) ++ w.toList = 0 :: xs ++ t :: w.toList := by simp
    rewrite [this, List.zeros_concat]
    dsimp [store_X_1_to_X_succ_n, concat_is_seq_execution]
    simp [execution_from_state]
    have := calc
          execution_from_state (0 :: (xs ++ t :: (Mathlib.Vector.toList w ++ (List.zeros (n + 1) ++ [0]))))
            (store_X_1_to_X_succ_n (n + 1 + c + 2) n)
        = execution_from_state (0 :: xs ++ t :: Mathlib.Vector.toList w ++ List.zeros (n + 1) ++ [0])
            (store_X_1_to_X_succ_n (n + 1 + c + 2) n) := by simp
      _ = execution_from_state (0 :: xs ++ t :: Mathlib.Vector.toList w ++ List.zeros (n + 1))
            (store_X_1_to_X_succ_n (n + 1 + c + 2) n) ++ [0] := by
              have l_h : (0 :: xs ++ t :: w.toList ++ List.zeros (n + 1)).length = n + n + c + 4 := by simp_arith [xs_l]
              have : highest_var (store_X_1_to_X_succ_n (n + 1 + c + 2) n) = n + n + c + 3 := by
                rewrite [highest_var_store]
                have : n + 1 ≤ n + 1 + (c + 2 + n) := Nat.le_add_right (n + 1) (c + 2 + n)
                repeat rewrite [←Nat.add_assoc] at this
                rewrite [Nat.max_eq_right this]
                simp_arith
              have : n + n + c + 3 ≥ highest_var (store_X_1_to_X_succ_n (n + 1 + c + 2) n) := by
                rewrite [this]
                exact Nat.le_refl _
              have := @execution_from_state_gt_highest_append (store_X_1_to_X_succ_n (n + 1 + c + 2) n) [0] (n + n + c + 3)
                ⟨(0 :: xs ++ t :: w.toList ++ List.zeros (n + 1)), l_h⟩ this
              simp at this
              simp
              exact this
      _ = 0 :: xs ++ t :: w.toList ++ xs ++ [0] := by
        have := n_ih (c + 1) ⟨(t :: w.toList), by simp_arith⟩ ⟨xs, xs_l⟩
        have := congrArg (· ++ [0]) this
        simp at this
        rewrite [Nat.add_comm c 1] at this
        repeat rewrite [←Nat.add_assoc] at this
        simp
        assumption

    rewrite [this]
    have : (0 :: xs ++ t :: Mathlib.Vector.toList w ++ xs).length = n + 1 + c + 2 + n + 1 := by simp_arith [xs_l]
    rewrite [inc_X_i_X_j_adds_value this]
    have : value_at (0 :: xs ++ t :: Mathlib.Vector.toList w ++ xs ++ [0]) (n + 2) = t := by
      have : 0 :: xs ++ t :: w.toList ++ xs ++ [0] = 0 :: xs ++ t :: (w.toList ++ xs ++ [0]) := by simp
      rewrite [this]
      have : (0 :: xs).length = n + 2 := by simp_arith [xs_l]
      exact value_at_n this
    simp [this]
    simp at this
    assumption

theorem inc_X_i_X_j_succ : execution_from_state (x :: xs) (X (i + 1) += X (j + 1))
    = x :: execution_from_state xs (X i += X j) := by
  simp [inc_X_i_X_j, execution_from_state]
  rewrite [value_at_cons_succ]
  generalize value_at xs j = n
  induction n
  case zero =>
    simp [loop_n_times]
  case succ n n_ih =>
    simp [loop_n_times_loop]
    rewrite [n_ih]
    simp [execution_from_state]
    rw [inc_value_cons_succ]

theorem setup_X_succ : execution_from_state (x :: xs) (setup_X_j_to_X_n_plus_j (offset + 1) (j + 1) n)
    = x :: execution_from_state xs (setup_X_j_to_X_n_plus_j offset j n) := by
  induction n
  case zero =>
    dsimp [setup_X_j_to_X_n_plus_j]
    rw [inc_X_i_X_j_succ]
  case succ n n_ih =>
    dsimp [setup_X_j_to_X_n_plus_j]
    simp [concat_is_seq_execution, execution_from_state]
    rewrite [n_ih, ←Nat.add_assoc]
    rewrite [inc_X_i_X_j_succ]
    simp_arith

theorem lemma_setup : ∀ c n : Nat, ∀ w : VectNat c, ∀ v : VectNat (n + 1),
    execution_from_state (List.zeros (n + 1) ++ w.toList ++ v.toList) (setup_X_j_to_X_n_plus_j (n + c) 0 n)
      = v.toList ++  w.toList ++ v.toList := by
  intro c n
  revert c
  induction n
  case zero =>
    intro c w v
    let ⟨[x], xs_l⟩ := v
    simp [Mathlib.Vector.head, setup_X_j_to_X_n_plus_j]
    have := @inc_X_i_X_j_adds_value 0 [] 0 (w.toList ++ [x]) (c + 1) rfl
    simp at this
    rewrite [this]
    repeat rewrite [←List.cons_append]
    have : (0 :: w.toList).length = c + 1 := by simp
    rw [value_at_n this]
  case succ n n_ih =>
    intro c w v
    let xs := v.toList.take (n + 1)
    have := List.ne_nil_of_length_eq_add_one v.length_val
    let t := v.toList.getLast this
    have v_list : v.toList = xs ++ [t] := List.take_n_concat_last_eq _ (by simp [this])
    rewrite [v_list]
    have xs_l : xs.length = n + 1 := by
      have : (xs ++ [t]).length = v.toList.length := by rw [v_list]
      simp [List.length_concat] at this
      assumption
    simp_arith
    dsimp [setup_X_j_to_X_n_plus_j, concat_is_seq_execution]
    simp [execution_from_state]
    rewrite [List.zeros_concat]
    have := calc
          execution_from_state ((List.zeros (n + 1) ++ [0] ++ (w.toList ++ (xs ++ [t]))))
            (setup_X_j_to_X_n_plus_j (n + 1 + c) 0 n)
        = execution_from_state (List.zeros (n + 1) ++ 0 :: w.toList ++ xs ++ [t])
            (setup_X_j_to_X_n_plus_j (n + c + 1) 0 n) := by rewrite [Nat.add_comm, Nat.add_assoc, Nat.add_comm 1 (n + c)]; simp

      _ = (execution_from_state (List.zeros (n + 1) ++ 0 :: w.toList ++ xs)
            (setup_X_j_to_X_n_plus_j (n + c + 1) 0 n)) ++ [t] := by
            have : highest_var (setup_X_j_to_X_n_plus_j (n + c + 1) 0 n) ≤ (2*n + c + 2) := by
              have : highest_var (setup_X_j_to_X_n_plus_j (n + c + 1) 0 n) = (2*n + c + 2) := by rewrite [highest_var_setup] ; simp_arith
              rewrite [this]
              exact Nat.le_refl _
            have := @execution_from_state_gt_highest_append (setup_X_j_to_X_n_plus_j (n + c + 1) 0 n) [t] (2*n + c + 2)
              ⟨List.zeros (n + 1) ++ 0 :: w.toList ++ xs, by simp_arith [xs_l]⟩ this
            simp at this
            simp
            rw [this]
      _ = xs ++ 0 :: w.toList ++ xs ++ [t] := by
        have := n_ih (c + 1) ⟨0 :: w.toList, by simp⟩ ⟨xs, xs_l⟩
        simp_arith at this
        rewrite [←Nat.add_assoc] at this
        simp
        rewrite [this]
        simp

    rewrite [this]
    simp_arith
    have := @inc_X_i_X_j_adds_value (n + 1) xs 0 (w.toList ++ xs ++ [t]) (2*n + c + 3) xs_l
    simp at this
    rewrite [this]
    have := @value_at_n (2*n + c + 3) (xs ++ 0 :: w.toList ++ xs) t [] (by simp_arith [xs_l])
    simp at this
    rewrite [this]
    simp

theorem lemma_setup_X_1 : ∀ c n : Nat, ∀ w : VectNat c, ∀ v : VectNat (n + 1),
    execution_from_state (0 :: List.zeros (n + 1) ++ w.toList ++ v.toList) (setup_X_j_to_X_n_plus_j (n + c + 1) 1 n)
      = 0 :: v.toList ++  w.toList ++ v.toList := by
  intros
  repeat rewrite [List.cons_append]
  repeat rewrite [List.append_assoc]
  rewrite [setup_X_succ]
  repeat rewrite [←List.append_assoc]
  rw [lemma_setup]

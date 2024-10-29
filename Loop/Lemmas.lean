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

theorem init_state_eq : init_state v = 0 :: v.toList := rfl

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

theorem concat_eq_seq_execution {p p' : Program} : p ++ p' = seq_execution p p' := rfl

theorem seq_execution_unfold : execution_from_state xs (seq_execution p p')
  = execution_from_state (execution_from_state xs p) p' := by simp only [execution_from_state]

theorem List.zeros_zero : List.zeros 0 = [] := rfl

theorem List.zeros_succ : List.zeros (n + 1) = 0 :: List.zeros n := by
  simp only [List.zeros, List.replicate]

theorem List.zeros_length : (List.zeros n).length = n := by
  dsimp [List.zeros]
  rw [List.length_replicate]

theorem value_at_zeros_eq_zero (n k : Nat) : value_at (List.zeros n) k = 0 := by
  revert n
  induction k
  all_goals intro n; cases n <;> simp only [List.zeros_zero, List.zeros_succ, value_at_nil,
    value_at_cons_zero, value_at_cons_succ, *]

theorem append_zeros_does_not_change_value_at (xs : VarState) (n k : Nat) :
    value_at xs k = value_at (xs ++ List.zeros n) k := by
  revert k
  induction xs
  case nil => simp [value_at_nil, value_at_zeros_eq_zero]
  case cons _ tail tail_ih =>
    intro k
    cases k <;> simp [value_at_cons_zero, value_at_cons_succ, tail_ih]

theorem clear_value_clears_value (xs : VarState) :
    value_at (clear_value xs n) k = if (n = k) then 0 else value_at xs k := by
  revert n k
  induction xs
  case nil =>
    simp [clear_value_nil, value_at_nil]
  case cons x xs xs_ih =>
    intro n k
    cases n
    · cases k <;> dsimp [clear_value, value_at]
    · cases k
      · dsimp [clear_value, value_at]
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
      dsimp [inc_value_nil_zero, value_at_nil]
      intro k
      cases k <;> dsimp [value_at]
    case succ _ n_ih =>
      dsimp [inc_value, value_at_nil]
      intro k
      cases k
      · dsimp [value_at_cons_zero]
      · simp [value_at_cons_succ]
        dsimp [value_at_nil] at n_ih
        exact n_ih
  case cons x xs xs_ih =>
    intro n
    cases n
    · dsimp [inc_value_cons_zero, value_at_cons_succ]
      intro k
      cases k <;> dsimp [value_at]
    · simp [inc_value_cons_succ]
      intro k
      cases k <;> simp [value_at_cons_zero, value_at_cons_succ, xs_ih]

theorem loop_inc_adds_value :
    execution_from_state (x :: xs) (LOOP X n DO INC X 0 END) = (x + value_at (x :: xs) n) :: xs := by
  simp only [execution_from_state]
  generalize value_at (x :: xs) n = k
  revert x
  induction k
  all_goals simp_arith [loop_n_times, execution_from_state, inc_value, *]

theorem same_values_same_execution (p : Program) (xs ys : VarState) :
    (∀ k : Nat, value_at xs k = value_at ys k) → ∀ k : Nat, value_at (execution_from_state xs p) k
      = value_at (execution_from_state ys p) k := by
  revert xs ys
  induction p
  case clear_var n =>
    intro xs ys h _
    simp only [execution_from_state, clear_value_clears_value, h]
  case increment_var n =>
    intro xs ys h _
    simp only [execution_from_state, inc_value_increments_value, h]
  case loop_var n inner inner_ih =>
    intro xs ys h
    simp only [execution_from_state, h]
    generalize value_at ys n = x
    revert xs ys
    induction x
    case zero =>
      intro _ _ h
      simp [loop_n_times, h]
    case succ _ x_ih =>
      intro xs ys h
      simp only [loop_n_times]
      apply x_ih (execution_from_state xs inner) (execution_from_state ys inner)
      exact inner_ih xs ys h
  case seq_execution _ _ p_ih p'_ih =>
    intros
    simp only [execution_from_state]
    apply p'_ih
    apply p_ih
    assumption

theorem append_zeros_does_not_change_execution (n k : Nat) :
     value_at (execution_from_state xs p) k = value_at (execution_from_state (xs ++ List.zeros n) p) k:=
  same_values_same_execution p xs (xs ++ List.zeros n) (append_zeros_does_not_change_value_at xs n) k

theorem clear_value_clears_succ_largest_index (xs : VarState) (l_h : xs.length ≥ k + 1) :
    clear_value (xs ++ ys) k = (clear_value xs k) ++ ys := by
  revert k
  induction xs
  case nil =>
    intros
    contradiction
  case cons _ _ xs_ih =>
    intro k
    cases k
    · simp [clear_value]
    · simp [clear_value_cons_succ]
      exact xs_ih

theorem inc_value_increments_succ_largest_index (xs : VarState) (l_h : xs.length ≥ k + 1) :
    inc_value (xs ++ ys) k = (inc_value xs k) ++ ys := by
  revert k
  induction xs
  case nil =>
    intros
    contradiction
  case cons _ _ xs_ih =>
      intro k
      cases k
      · simp [inc_value]
      · simp [inc_value_cons_succ]
        exact xs_ih

theorem value_at_first_k (v : VectNat n) (n_h : n > k) :
    value_at (v.toList ++ xs) k = value_at v.toList k := by
  revert k
  induction n
  case zero =>
    intros
    contradiction
  case succ _ n_ih =>
    let ⟨ys, ys_l⟩ := v
    simp
    cases ys
    case nil =>
      intros
      contradiction
    case cons _ ys =>
      intro k k_h
      cases k
      case zero =>
        dsimp [value_at_cons_zero]
      case succ k =>
        simp [value_at_cons_succ]
        rewrite [List.length, Nat.succ_inj] at ys_l
        have := n_ih ⟨ys, ys_l⟩ (Nat.lt_of_succ_lt_succ k_h)
        dsimp at this
        assumption

theorem execution_from_state_long_enough_preserves_length (p : Program) (v : VectNat n) (n_h : n ≥ highest_var p + 1) :
    (execution_from_state v.toList p).length = n := by
  revert n
  induction p
  case clear_var k =>
    induction k
    case zero =>
      intro n v n_h
      dsimp [highest_var] at n_h
      cases n
      case zero =>
        contradiction
      case succ n =>
        let ⟨x :: xs, xs_l⟩ := v
        simp at xs_l
        simp [execution_from_state, clear_value, xs_l]
    case succ k k_ih =>
      intro n v n_h
      dsimp [highest_var] at n_h
      cases n
      case zero =>
        contradiction
      case succ n =>
        simp at n_h
        let ⟨x :: xs, xs_l⟩ := v
        simp [execution_from_state, clear_value_cons_succ]
        simp at xs_l
        have := k_ih ⟨xs, xs_l⟩ n_h
        simp only [execution_from_state] at this
        assumption

  case increment_var k =>
    induction k
    case zero =>
      intro n v n_h
      dsimp [highest_var] at n_h
      cases n
      case zero =>
        contradiction
      case succ n =>
        let ⟨x :: xs, xs_l⟩ := v
        simp at xs_l
        simp [execution_from_state, inc_value, xs_l]
    case succ k k_ih =>
      intro n v n_h
      dsimp [highest_var] at n_h
      cases n
      case zero =>
        contradiction
      case succ n =>
        simp at n_h
        let ⟨x :: xs, xs_l⟩ := v
        simp [execution_from_state, inc_value_cons_succ]
        simp at xs_l
        have := k_ih ⟨xs, xs_l⟩ n_h
        simp only [execution_from_state] at this
        assumption

  case loop_var k inner inner_ih =>
    simp only [execution_from_state]
    intro n v
    generalize value_at v.toList k = m
    revert n v
    induction m
    case zero =>
      simp [loop_n_times]
    case succ _ m_ih =>
      intro n v n_h
      simp only [loop_n_times]
      let ys := execution_from_state v.toList inner
      dsimp [highest_var] at n_h
      have : highest_var inner + 1 ≤ n := by
        have : highest_var inner + 1 ≤ max k (highest_var inner) + 1 := by simp
        exact Nat.le_trans this n_h
      let w' : VectNat n := ⟨ys, inner_ih v this⟩
      have : execution_from_state v.toList inner = w'.toList := rfl
      rewrite [this]
      exact m_ih w' n_h

  case seq_execution p p' p_ih p'_ih =>
    intro n v n_h
    let ys := execution_from_state v.toList p
    have : n ≥ highest_var p + 1 := by
      rewrite [highest_var] at n_h
      have : max (highest_var p) (highest_var p') + 1 ≥ highest_var p + 1 := by simp
      exact Nat.le_trans this n_h
    let w' : VectNat n := ⟨ys, p_ih v this⟩
    simp only [execution_from_state]
    have : execution_from_state v.toList p = w'.toList := rfl
    rewrite [this]
    have : n ≥ highest_var p' + 1 := by
      rewrite [highest_var] at n_h
      have : max (highest_var p) (highest_var p') + 1 ≥ highest_var p' + 1 := by simp
      exact Nat.le_trans this n_h
    exact p'_ih w' this

-- Maybe remove this
theorem execution_from_state_gt_highest_append_vector {n : Nat} (v : VectNat (n + 1)) (n_h : n ≥ highest_var p) :
    execution_from_state (v.toList ++ xs) p = (execution_from_state v.toList p) ++ xs := by
  revert n
  induction p
  case clear_var k =>
    intro n v n_h
    simp only [execution_from_state]
    have : v.toList.length ≥ k + 1 := by
      have : k ≤ n := by dsimp [highest_var] at n_h; assumption
      simp [this]
    exact clear_value_clears_succ_largest_index v.toList this
  case increment_var k =>
    intro n v n_h
    simp only [execution_from_state]
    have : v.toList.length ≥ k + 1 := by
      have : k ≤ n := by dsimp [highest_var] at n_h; assumption
      simp [this]
    exact inc_value_increments_succ_largest_index v.toList this
  case loop_var k inner inner_ih =>
    intro n v n_h
    simp only [execution_from_state]
    have : value_at (v.toList ++ xs) k = value_at v.toList k := by
      have : n ≥ k := by
        dsimp [highest_var] at n_h
        exact Nat.le_trans (Nat.le_max_left _ _) n_h
      exact value_at_first_k v (Nat.lt_succ_of_le this)
    rewrite [this]
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
        dsimp [highest_var] at n_h
        exact Nat.le_trans (Nat.le_max_right _ _) n_h
      rewrite [inner_ih v this]
      let ys := execution_from_state v.toList inner
      have : ys.length = n + 1 := execution_from_state_long_enough_preserves_length inner v (Nat.add_le_add_right this 1)
      let v' : VectNat (n + 1) := ⟨ys, this⟩
      have : execution_from_state v.toList inner = v'.toList := rfl
      rewrite [this]
      have : value_at (v'.toList ++ xs) k = value_at v'.toList k := by
        have : n ≥ k := by
          dsimp [highest_var] at n_h
          exact Nat.le_trans (Nat.le_max_left _ _) n_h
        exact value_at_first_k v' (Nat.lt_succ_of_le this)
      exact m_ih v' n_h this

  case seq_execution p p' p_ih p'_ih =>
    intro n v n_h
    simp only [execution_from_state]
    have : n ≥ highest_var p := by
        dsimp [highest_var] at n_h
        exact Nat.le_trans (Nat.le_max_left _ _) n_h
    rewrite [p_ih v this]
    let ys := execution_from_state v.toList p
    have : ys.length = n + 1 := execution_from_state_long_enough_preserves_length p v (Nat.add_le_add_right this 1)
    let v' : VectNat (n + 1) := ⟨ys, this⟩
    have : execution_from_state v.toList p = v'.toList := rfl
    rewrite [this]
    have : n ≥ highest_var p' := by
      dsimp [highest_var] at n_h
      exact Nat.le_trans (Nat.le_max_right _ _) n_h
    exact p'_ih v' this

theorem execution_from_state_gt_highest_append_list {xs : VarState} (n_h : xs.length ≥ highest_var p + 1) :
    execution_from_state (xs ++ ys) p = (execution_from_state xs p) ++ ys := by
  have := calc
    1 ≤ highest_var p + 1 := by simp_arith
    _ ≤ xs.length := n_h
  have xs_l' := (Nat.sub_add_cancel this).symm
  have : List.length xs - 1 ≥ highest_var p := by
    have := Nat.sub_le_sub_right n_h 1
    rewrite [Nat.add_sub_cancel] at this
    assumption
  have := @execution_from_state_gt_highest_append_vector p ys (xs.length - 1) ⟨xs, xs_l'⟩ this
  dsimp at this
  assumption


theorem execution_from_init_state_ge_highest_append (v : VectNat n) (n_h : n ≥ highest_var p) :
    execution_from_state (init_state v ++ xs) p = (execution_from_state (init_state v) p) ++ xs :=
  execution_from_state_gt_highest_append_vector (0 ::ᵥ v) n_h

theorem execution_from_state_append_xs (v : VectNat n) :
    execution_from_state (init_state v ++ List.zeros (highest_var p - n) ++ xs) p
    = (execution_from_state (init_state v ++ List.zeros (highest_var p - n)) p) ++ xs := by
  rewrite [init_state]
  let ys := v.toList ++ List.zeros (highest_var p - n)
  let m := ys.length
  have m_h : m ≥ highest_var p := by
    simp [m, ys]
    rewrite [Nat.add_comm, Nat.sub_add_eq_max]
    exact Nat.le_max_left _ _
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
    rewrite [Nat.add_comm, Nat.max_eq_left k_h] at this
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

theorem highest_var_concat : highest_var (p1 ++ p2) = max (highest_var p1) (highest_var p2) := by dsimp [highest_var]

theorem loop_n_times_loop : loop_n_times (n + 1) xs p = execution_from_state (loop_n_times n xs p) p := by
  revert xs
  induction n
  case zero =>
    simp [loop_n_times]
  case succ n n_ih =>
    intro xs
    have : loop_n_times ((n + 1) + 1) xs p = loop_n_times (n + 1) (execution_from_state xs p) p := by simp only [loop_n_times]
    rw [this, n_ih, ←loop_n_times]

theorem value_at_n : (xs.length = n) →
    value_at (xs ++ y :: ys) n = y := by
  revert xs
  induction n
  case zero =>
    simp [value_at_cons_zero]
  case succ _ n_ih =>
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
  case succ _ n_ih =>
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
  case succ _ n_ih =>
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
    simp only [execution_from_state]
    rw [inc_value_at_n xs_l, Nat.add_assoc y k 1]

theorem nested_max_lemma {a b : Nat} :
    max (max a b) (max (a + 1) (b + 1)) = max (a + 1) (b + 1) := by
  cases Nat.decLe a b
  case isTrue h =>
    repeat rewrite [Nat.max_def]
    simp [h]
  case isFalse h =>
    repeat rewrite [Nat.max_def]
    simp [h]

theorem List.take_n_concat_last_eq (xs : List α) (xs_l : xs.length = n + 1) :
    xs = xs.take n ++ [xs.getLast (List.ne_nil_of_length_eq_add_one xs_l)] := by
  revert xs
  induction n
  case zero =>
    intro xs _
    let [x] := xs
    dsimp [List.take]
  case succ n n_ih =>
    intro xs xs_l
    let (x :: xs) := xs
    simp at xs_l
    dsimp [List.take]
    rewrite [List.cons_inj_right, List.getLast_cons (List.ne_nil_of_length_eq_add_one xs_l)]
    exact n_ih xs xs_l

  def cons_last_construction (v : Mathlib.Vector α (n + 1)) :
      (t : α) ×' (xs : List α) ×' (xs.length = n) ×' (v.toList = xs ++ [t]) :=
    let t := v.toList.getLast (List.ne_nil_of_length_eq_add_one v.length_val)
    let xs := v.toList.take n
    let v_list : v.toList = xs ++ [t] := List.take_n_concat_last_eq v.toList (v.length_val)
    let xs_l : xs.length = n := by
      have := congrArg (List.length) v_list
      simp [List.length_append] at this
      exact this.symm
    ⟨t, xs, xs_l, v_list⟩


theorem List.zeros_concat : List.zeros (n + 1) = List.zeros n ++ [0] := by
  have := take_n_concat_last_eq (zeros (n + 1)) List.zeros_length
  simp at this
  rewrite [←List.zeros] at this
  assumption

-- Note: attempting to use the simplifier does not work. Why?
theorem max_le_lemma {a b c d : Nat} (h_1 : a ≤ c) (h_2 : b ≤ d) : max a b ≤ max c d := by
  have h_3 := Nat.le_trans h_1 (Nat.le_max_left c d)
  have h_4 := Nat.le_trans h_2 (Nat.le_max_right c d)
  exact Nat.max_le.mpr (And.intro h_3 h_4)

theorem highest_var_store : highest_var (store_X_1_to_X_succ_n idx n) = max (n + 1) (idx + n) := by
  induction n
  case zero =>
    dsimp [store_X_1_to_X_succ_n, highest_var]
  case succ n n_ih =>
    dsimp [store_X_1_to_X_succ_n, highest_var]
    rewrite [n_ih, ←Nat.add_assoc idx n 1]
    rw [Nat.max_eq_right (max_le_lemma (Nat.le_succ (n + 1)) (Nat.le_succ (idx + n)))]

theorem highest_var_clear : highest_var (clear_X_j_to_X_n_plus_j j n) = n + j := by
  induction n
  case zero =>
    dsimp [clear_X_j_to_X_n_plus_j, highest_var]
    exact (Nat.zero_add j).symm
  case succ n n_ih =>
    dsimp [clear_X_j_to_X_n_plus_j, highest_var]
    have : n + 1 + j = n + j + 1 := by simp_arith
    rw [n_ih, this, Nat.max_eq_right (Nat.le_succ (n + j))]

theorem highest_var_setup : highest_var (setup_X_j_to_X_n_plus_j idx j n) = max (n + j) (idx + n + 1) := by
  induction n
  case zero =>
    dsimp [setup_X_j_to_X_n_plus_j, highest_var]
    rw [Nat.zero_add, Nat.max_comm]
  case succ n n_ih =>
    dsimp [setup_X_j_to_X_n_plus_j, highest_var]
    rewrite [n_ih, Nat.max_comm (n + j)]
    have : n + 1 + j = n + j + 1 := by simp_arith
    rewrite [this, ←Nat.add_assoc]
    rewrite [Nat.max_eq_right (max_le_lemma (Nat.le_succ (idx + n + 1)) (Nat.le_succ (n + j)))]
    rw [Nat.max_comm]

theorem highest_var_clear_Z (n : Nat) : highest_var (clear_Z_0_to_Z_n idx n) = idx + n:= by
  induction n
  case zero =>
    dsimp [highest_var]
  case succ n n_ih =>
    dsimp [highest_var]
    rw [n_ih, Nat.max_eq_right (Nat.le_succ (idx + n)), ←Nat.add_assoc]

theorem clear_Z_succ : execution_from_state (x :: xs) (clear_Z_0_to_Z_n (k + 1) n)
    = x :: execution_from_state xs (clear_Z_0_to_Z_n k n) := by
  induction n
  case zero =>
    dsimp [clear_Z_0_to_Z_n]
    simp only [execution_from_state]
    rw [clear_value_cons_succ]
  case succ n n_ih =>
    dsimp [clear_Z_0_to_Z_n, concat_eq_seq_execution]
    simp only [execution_from_state]
    rewrite [n_ih, clear_value_cons_succ]
    rw [Nat.add_assoc, Nat.add_comm 1 n, Nat.add_assoc]

theorem clear_Z_lemma (v : VectNat (n + 1)) : (xs.length = k) →
    execution_from_state (xs ++ v.toList) (clear_Z_0_to_Z_n k n)
      = xs ++ List.zeros (n + 1) := by
  revert xs
  induction k
  case zero =>
    intro xs xs_l
    rewrite [List.eq_nil_of_length_eq_zero xs_l, List.nil_append, List.nil_append]
    revert v
    induction n
    case zero =>
      intros
      simp [clear_Z_0_to_Z_n, execution_from_state, clear_value]
    case succ n n_ih =>
      intro v
      dsimp [clear_Z_0_to_Z_n, concat_eq_seq_execution]
      simp [execution_from_state]
      let ⟨t, xs, xs_l, v_list⟩ := cons_last_construction v
      rewrite [v_list]
      have : xs.length ≥ highest_var (clear_Z_0_to_Z_n 0 n) + 1 := by simp [highest_var_clear_Z, xs_l]
      rewrite [execution_from_state_gt_highest_append_list this]
      have := n_ih ⟨xs, xs_l⟩
      dsimp at this
      rewrite [this, clear_value_at_n (@List.zeros_length (n + 1))]
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
    simp [clear_X_j_to_X_n_plus_j, concat_eq_seq_execution, execution_from_state]
    rw [n_ih, ←Nat.add_assoc, clear_value_cons_succ]

theorem clear_X_lemma (v : VectNat (n + 1)) : execution_from_state v.toList (clear_X_j_to_X_n_plus_j 0 n)
    = List.zeros (n + 1) := by
  induction n
  case zero =>
    simp [clear_X_j_to_X_n_plus_j, execution_from_state, clear_value]
  case succ n n_ih =>
    simp [clear_X_j_to_X_n_plus_j, concat_eq_seq_execution, execution_from_state]
    let ⟨t, xs, xs_l, v_list⟩ := cons_last_construction v
    rewrite [v_list]
    have : highest_var (clear_X_j_to_X_n_plus_j 0 n) + 1 ≤ xs.length := by
      rewrite [xs_l, Nat.succ_le_succ_iff]
      have : highest_var (clear_X_j_to_X_n_plus_j 0 n) = n := highest_var_clear
      rewrite [this]
      exact Nat.le_refl _
    rewrite [execution_from_state_gt_highest_append_list this]
    have := n_ih ⟨xs, xs_l⟩
    dsimp at this
    rewrite [this, clear_value_at_n (@List.zeros_length (n + 1))]
    rw [←List.zeros_concat]

theorem clear_X_1_lemma (v : VectNat (n + 1)) : execution_from_state (0 :: v.toList) (clear_X_j_to_X_n_plus_j 1 n)
    = 0 :: List.zeros (n + 1) := by
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
    repeat rewrite [← List.cons_append]
    let ys := 0 :: x :: w.toList
    have : ys.length = c + 2 := by
      dsimp [ys]
      rw [w.toList_length]
    rewrite [inc_X_i_X_j_adds_value this]
    simp [ys, value_at]
  case succ n n_ih =>
    intro c w v
    let ⟨t, xs, xs_l, v_list⟩ := cons_last_construction v
    rewrite [v_list, ←List.cons_append, List.zeros_concat, ←List.append_assoc]
    simp only [store_X_1_to_X_succ_n, concat_eq_seq_execution, execution_from_state]
    rewrite [←List.append_cons _ t]
    have := calc
          execution_from_state (0 :: xs ++ t :: Mathlib.Vector.toList w ++ List.zeros (n + 1) ++ [0])
            (store_X_1_to_X_succ_n (n + 1 + c + 2) n)
      _ = execution_from_state (0 :: xs ++ t :: Mathlib.Vector.toList w ++ List.zeros (n + 1))
            (store_X_1_to_X_succ_n (n + 1 + c + 2) n) ++ [0] := by
              have l_h : (0 :: xs ++ t :: w.toList ++ List.zeros (n + 1)).length = n + n + c + 4 := by simp_arith [xs_l]
              have : highest_var (store_X_1_to_X_succ_n (n + 1 + c + 2) n) = n + n + c + 3 := by
                rewrite [highest_var_store]
                have : n + 1 ≤ n + 1 + (c + 2 + n) := Nat.le_add_right (n + 1) (c + 2 + n)
                repeat rewrite [←Nat.add_assoc] at this
                rewrite [Nat.max_eq_right this]
                simp_arith
              have : (0 :: xs ++ t :: w.toList ++ List.zeros (n + 1)).length
                  ≥ highest_var (store_X_1_to_X_succ_n (n + 1 + c + 2) n) + 1 := by
                rewrite [l_h, this]
                exact Nat.le_refl _
              rw [execution_from_state_gt_highest_append_list this]
      _ = 0 :: xs ++ t :: w.toList ++ xs ++ [0] := by
        have := congrArg (· ++ [0]) (n_ih (c + 1) ⟨(t :: w.toList), by simp⟩ ⟨xs, xs_l⟩)
        dsimp at this
        repeat rewrite [←List.cons_append] at this
        rewrite [Nat.add_comm c 1, ←Nat.add_assoc] at this
        rw [this]
    rewrite [this]
    have : (0 :: xs ++ t :: Mathlib.Vector.toList w ++ xs).length = n + 1 + c + 2 + n + 1 := by simp_arith [xs_l]
    rewrite [inc_X_i_X_j_adds_value this]
    have : value_at (0 :: xs ++ t :: Mathlib.Vector.toList w ++ xs ++ [0]) (n + 2) = t := by
      have : 0 :: xs ++ t :: w.toList ++ xs ++ [0] = 0 :: xs ++ t :: (w.toList ++ xs ++ [0]) := by simp
      rewrite [this]
      have : (0 :: xs).length = n + 2 := by simp [xs_l]
      exact value_at_n this
    rewrite [this]
    simp

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
    simp only [execution_from_state]
    rw [inc_value_cons_succ]

theorem setup_X_succ : execution_from_state (x :: xs) (setup_X_j_to_X_n_plus_j (offset + 1) (j + 1) n)
    = x :: execution_from_state xs (setup_X_j_to_X_n_plus_j offset j n) := by
  induction n
  case zero =>
    dsimp [setup_X_j_to_X_n_plus_j]
    rw [inc_X_i_X_j_succ]
  case succ n n_ih =>
    dsimp [setup_X_j_to_X_n_plus_j]
    simp [concat_eq_seq_execution, execution_from_state]
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
    dsimp [setup_X_j_to_X_n_plus_j]
    have : (0 :: w.toList).length = c + 1 := by simp_all
    rewrite [Nat.zero_add, ←List.nil_append (0 :: (w.toList ++ [x]))]
    rewrite [inc_X_i_X_j_adds_value (by simp), ←List.cons_append]
    simp only [List.nil_append, Nat.add_zero]
    have : (0 :: w.toList).length = c + 1 := by simp
    rewrite [value_at_n this]
    simp
  case succ n n_ih =>
    intro c w v
    let ⟨t, xs, xs_l, v_list⟩ := cons_last_construction v
    rewrite [v_list, ←List.append_assoc, List.zeros_concat, ←List.append_cons]
    simp only [setup_X_j_to_X_n_plus_j, concat_eq_seq_execution, execution_from_state]

    have := calc
          execution_from_state (List.zeros (n + 1) ++ 0 :: w.toList ++ xs ++ [t])
            (setup_X_j_to_X_n_plus_j (n + 1 + c) 0 n)
        = (execution_from_state (List.zeros (n + 1) ++ 0 :: w.toList ++ xs)
            (setup_X_j_to_X_n_plus_j (n + 1 + c) 0 n)) ++ [t] := by

            have : (List.zeros (n + 1) ++ 0 :: Mathlib.Vector.toList w ++ xs).length
                ≥ highest_var (setup_X_j_to_X_n_plus_j (n + 1 + c) 0 n) + 1 := by
              simp_arith [xs_l]
              have : highest_var (setup_X_j_to_X_n_plus_j (n + 1 + c) 0 n)
                = (2*n + c + 2) := by rewrite [highest_var_setup] ; simp_arith
              rewrite [this]
              exact Nat.le_refl _

            rw [execution_from_state_gt_highest_append_list this]
      _ = xs ++ 0 :: w.toList ++ xs ++ [t] := by
        have := n_ih (c + 1) ⟨0 :: w.toList, by simp⟩ ⟨xs, xs_l⟩
        dsimp at this
        rewrite [Nat.add_comm c 1, ←Nat.add_assoc] at this
        rw [this]
    rewrite [this]
    rewrite [List.append_assoc, List.append_assoc, List.cons_append]
    rewrite [inc_X_i_X_j_adds_value xs_l]
    repeat rewrite [←List.cons_append]
    repeat rewrite [←List.append_assoc]
    have : (xs ++ 0 :: w.toList ++ xs).length = n + 1 + c + n + 2 := by simp_arith [xs_l]
    rw [value_at_n this, Nat.zero_add]

theorem lemma_setup_X_1 : ∀ c n : Nat, ∀ w : VectNat c, ∀ v : VectNat (n + 1),
    execution_from_state (0 :: List.zeros (n + 1) ++ w.toList ++ v.toList) (setup_X_j_to_X_n_plus_j (n + c + 1) 1 n)
      = 0 :: v.toList ++  w.toList ++ v.toList := by
  intros
  repeat rewrite [List.cons_append]
  repeat rewrite [List.append_assoc]
  rewrite [setup_X_succ]
  repeat rewrite [←List.append_assoc]
  rw [lemma_setup]

--
theorem forall_exists_function {n : Nat} (g : Fin n → VectNat m → Nat)
    (g_h : ∀ i : Fin n, loop_computable_cleanly (g i)) :
    ∃ p_g : Fin n → Program, ∀ i, cleanly_computes (p_g i) (g i) := by
  induction n
  case zero =>
    exists Fin.elim0
    intro i
    exact i.elim0
  case succ n n_ih =>
    let g' : Fin n → VectNat m → Nat := fun i => g i
    have ⟨p_g', g_g'_h⟩ := n_ih g' (fun i => g_h i)
    have ⟨p_g_n, p_g_n_h⟩ := g_h ⟨n, Nat.lt_succ_self n⟩

    let p_g : Fin (n + 1) → Program := fun i => match (Nat.decLt i.val n) with
      | isTrue h => p_g' ⟨i.val, h⟩
      | isFalse _ => p_g_n

    exists p_g
    intro i
    dsimp [p_g]
    cases (Nat.decLt i.val n)
    case isTrue h =>
      dsimp
      have r := g_g'_h ⟨i.val, h⟩
      have : g' ⟨i.val, h⟩ = g i := by simp [g']
      rewrite [this] at r
      assumption
    case isFalse h =>
      dsimp
      suffices h : ⟨n, Nat.lt_succ_self n⟩ = i from by rewrite [h] at p_g_n_h; assumption
      suffices h : n = i.val from Fin.eq_of_val_eq h
      exact Nat.le_antisymm (Nat.ge_of_not_lt h) (Nat.le_of_lt_succ i.2)

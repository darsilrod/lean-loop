/-
Copyright: TODO
Authors: Darío Silva Rodríguez
-/

import Mathlib.Data.Vector.Defs
import Mathlib.Data.Vector.Basic
import Mathlib.Computability.Primrec
import Loop.Defs
import Loop.Lemmas

/-!
# The Loop programming language

The goal of this project is to formally define the semantics of the Loop
programming language, define what Loop-computable functions are, and prove that
Loop-computable is the same as primitive recursive.
-/

-- TODO: make constructive version

namespace Loop

open Program
open Mathlib (Vector)

theorem loop_computable_cleanly_is_loop_computable {f : VectNat n → Nat} :
    loop_computable_cleanly f → loop_computable f := by
  intro ⟨p, h⟩
  exists p
  apply funext
  intro v
  let dif := highest_var p - n
  exact calc
      ⟦ p ⟧^(n) v
  _ = value_at (execution_from_state (init_state v ++ List.zeros dif) p) 0 := append_zeros_does_not_change_execution dif 0
  _ = value_at (f v :: v.toList ++ List.zeros dif) 0 := by rw [h v]
  _ = f v := rfl

--

theorem zero_is_loop_computable_cleanly : loop_computable_cleanly fun _ : VectNat 0 => 0 := by
  let p := CLEAR X 0
  exists p
  intro v
  simp [init_state, highest_var, p, execution_from_state, clear_value]

theorem succ_is_loop_computable_cleanly : loop_computable_cleanly fun v : VectNat 1 => v.head + 1 := by
  let p₁ :=
    LOOP X 1 DO
      INC X 0
    END
  let p₂ := INC X 0

  let p := p₁ ++ p₂

  exists p
  intro v
  simp [init_state, highest_var]
  exact calc
    execution_from_state [0, v.head] p
      =
    inc_value (execution_from_state [0, v.head] p₁) 0 := by simp [p, concat_eq_seq_execution, execution_from_state, p₂]
    _ =
    inc_value [v.head, v.head] 0 := by simp [p₁, loop_inc_adds_value, value_at]
    _ = [v.head + 1, v.head] := rfl

theorem get_is_loop_computable_cleanly (i : Fin n) : loop_computable_cleanly (fun v => v.get i) := by
  let p :=
    LOOP X i + 1 DO
      INC X 0
    END
  exists p
  intro v
  have : i + 1 - n = 0 := by exact Nat.sub_eq_zero_iff_le.2 i.isLt
  simp [init_state, highest_var, this, p, execution_from_state,
    loop_inc_adds_value, value_at_cons_succ, value_at, Vector.get_eq_get]

section prec_is_loop_computable_cleanly_proof

variable
  {n : Nat}
  {f : VectNat n → Nat}
  {g : VectNat (n + 2) → Nat}
  (f_h : cleanly_computes p_f f)
  (g_h : cleanly_computes p_g g)

-- Part I: construction of the program

def offset_pr (_ : cleanly_computes p_f f) (_ : cleanly_computes p_g g) : Nat :=
  max (n + 2) (max (highest_var p_f) (highest_var p_g))

-- Step 1: compute f of the last n inputs
def prec_program_1 : Program :=
  let offset_pr := offset_pr f_h g_h
  let p_1_1 := store_X_1_to_X_succ_n (offset_pr + 1) n
  let p_1_2 := clear_X_j_to_X_n_plus_j 1 n
  let p_1_3 := match (generalizing := false) n with
    | 0 => p_f
    | n + 1 => setup_X_j_to_X_n_plus_j (offset_pr + 1) 1 n ++ p_f
  p_1_1 ++ p_1_2 ++ p_1_3

-- Step 2: compute g counter number of times, for each recursive step
def prec_program_2 : Program :=
  let offset_pr := offset_pr f_h g_h
  let p_2_1 := X 2 += X 0
  let p_2_2 := CLEAR X 0
  let p_2_3 := p_g
  let p_2_4 := CLEAR X 2
  let p_2_5 := INC X 1
  let loop_inner := p_2_1 ++ p_2_2 ++ p_2_3 ++ p_2_4 ++ p_2_5
  let p_loop := LOOP X (offset_pr + 1) DO loop_inner END
  match (generalizing := false) n with
    | 0 => p_loop
    | n + 1 => clear_X_j_to_X_n_plus_j 1 n ++ setup_X_j_to_X_n_plus_j (offset_pr + 1) 3 n ++ p_loop

-- Step 3: Clean up
def prec_program_3 : Program :=
  let offset_pr := offset_pr f_h g_h
  let p_3_1 := match (generalizing := false) n with
    | 0 => CLEAR X 1
    | n + 1 => CLEAR X 1 ++ clear_X_j_to_X_n_plus_j 3 n
  let p_3_2 := setup_X_j_to_X_n_plus_j offset_pr 1 n
  let p_3_3 := clear_Z_0_to_Z_n (offset_pr + 1) n
  p_3_1 ++ p_3_2 ++ p_3_3

def prec_program : Program :=
  let p_1 := prec_program_1 f_h g_h
  let p_2 := prec_program_2 f_h g_h
  let p_3 := prec_program_3 f_h g_h
  p_1 ++ p_2 ++ p_3

-- Part II: calculate the highest variable of the program

theorem highest_var_p_f_le_offset_pr (f_h : cleanly_computes p_f f) (g_h : cleanly_computes p_g g) :
  highest_var p_f ≤ offset_pr f_h g_h := by simp [offset_pr]

theorem highest_var_p_g_le_offset_pr (f_h : cleanly_computes p_f f) (g_h : cleanly_computes p_g g) :
  highest_var p_g ≤ offset_pr f_h g_h := by simp [offset_pr]

theorem n_plus_two_le_offset_pr (f_h : cleanly_computes p_f f) (g_h : cleanly_computes p_g g) :
  n + 2 ≤ offset_pr f_h g_h := Nat.le_max_left _ _

theorem offset_pr_minus_n (f_h : cleanly_computes p_f f) (g_h : cleanly_computes p_g g) :
    offset_pr f_h g_h - n ≥ 2 := by
  have := n_plus_two_le_offset_pr f_h g_h
  rw [Nat.add_comm] at this
  have := Nat.sub_le_sub_right this n
  rwa [Nat.add_sub_cancel] at this


-- Note: using the simplifier in goals with many nested max appears to be very
-- slow. For this reason, I have avoided using it directly in these proofs.
theorem prec_program_1_highest_var : highest_var (prec_program_1 f_h g_h) = offset_pr f_h g_h + 1 + n := by
  dsimp [prec_program_1]
  repeat rw [highest_var_concat]
  rw [highest_var_store, highest_var_clear]
  cases n
  case zero =>
    rw [@Nat.max_eq_right 1 _ (by simp), @Nat.max_eq_left _ 1 (by simp)]
    apply Nat.max_eq_left
    apply Nat.le_trans (highest_var_p_f_le_offset_pr f_h g_h)
    apply Nat.le_succ
  case succ n =>
    rw [highest_var_concat, highest_var_setup]
    rw [@Nat.max_eq_right (n + 1) _ (by simp)]
    rw [@Nat.max_eq_right (n + 1 + 1) _ (by simp_arith)]
    rw [@Nat.max_eq_left _ (n + 1 + 1) (by simp_arith)]
    rw [Nat.add_assoc _ n]
    apply Nat.max_eq_left
    rw [Nat.max_eq_left]
    apply Nat.le_trans (highest_var_p_f_le_offset_pr f_h g_h)
    rw [Nat.add_assoc]
    exact Nat.le_add_right _ _

theorem prec_program_2_highest_var : highest_var (prec_program_2 f_h g_h) = offset_pr f_h g_h + 1 + n := by
  cases n
  case zero =>
    dsimp [highest_var]
    rw [@Nat.max_eq_right 0 2 (Nat.zero_le _)]
    rw [@Nat.max_eq_left 2 0 (Nat.zero_le _)]
    rw [@Nat.max_eq_left _ 2 (Nat.le_max_left _ _)]
    rw [@Nat.max_eq_left _ 1 (by simp)]
    apply Nat.max_eq_left
    apply Nat.max_le_of_le_of_le
    · apply Nat.le_trans (n_plus_two_le_offset_pr f_h g_h)
      apply Nat.le_succ
    · apply Nat.le_trans (highest_var_p_g_le_offset_pr f_h g_h)
      simp
  case succ n =>
    dsimp [highest_var]
    rw [highest_var_clear, highest_var_setup]
    rw [@Nat.max_eq_right 0 2 (Nat.zero_le _)]
    rw [@Nat.max_eq_left 2 0 (Nat.zero_le _)]
    rw [@Nat.max_eq_left _ 2 (Nat.le_max_left _ _)]
    rw [@Nat.max_eq_left _ 1 (by simp)]
    rw [Nat.add_assoc _ n]
    rw [@Nat.max_eq_right (n + 3) _
      (Nat.le_trans (n_plus_two_le_offset_pr f_h g_h) (by simp_arith))]
    rw [@Nat.max_eq_right (n + 1) _ (Nat.le_add_left _ _)]
    rw [@Nat.max_eq_left (offset_pr f_h g_h + 1) _
      (Nat.max_le_of_le_of_le _ _)]
    apply Nat.max_eq_left (Nat.le_add_right _ _)
    · apply @Nat.le_trans 2 (n + 3) _ (by simp)
      exact Nat.le_trans (n_plus_two_le_offset_pr f_h g_h) (Nat.le_succ _)
    · exact Nat.le_trans (highest_var_p_g_le_offset_pr f_h g_h) (Nat.le_succ _)

theorem prec_program_3_highest_var : highest_var (prec_program_3 f_h g_h) = offset_pr f_h g_h + 1 + n := by
  cases n
  case zero =>
    dsimp [highest_var]
    rw [@Nat.max_eq_left _ 1 (Nat.le_add_left _ _)]
    rw [@Nat.max_eq_right 1 _ (Nat.le_add_left _ _)]
    rw [Nat.max_self _]
  case succ n =>
    dsimp [highest_var]
    rw [highest_var_clear, highest_var_setup, highest_var_clear_Z]
    rw [@Nat.max_eq_right 1 _ (by simp)]
    rw [@Nat.max_eq_right (offset_pr f_h g_h + 1 + n) _ (Nat.le_succ _)]
    rw [@Nat.max_eq_right _ (offset_pr f_h g_h + n + 1) (by simp)]
    rw [@Nat.max_eq_left (offset_pr f_h g_h + n + 2) _ (by simp)]
    rw [@Nat.max_eq_right _ (offset_pr f_h g_h + n + 2) (Nat.le_succ _)]
    rw [Nat.add_assoc _ 1, Nat.add_comm 1 n]
    rw [←Nat.add_assoc, ←Nat.add_assoc]
    rw [@Nat.max_eq_right (n + 3) _ _]
    rw [Nat.max_self _]
    simp_arith
    apply Nat.le_trans (n_plus_two_le_offset_pr f_h g_h)
    rw [Nat.add_assoc]
    exact Nat.le_add_right _ _

theorem prec_program_highest_var : highest_var (prec_program f_h g_h) = offset_pr f_h g_h + 1 + n := by
  dsimp [prec_program]
  repeat rw [highest_var_concat]
  rw [prec_program_1_highest_var, prec_program_2_highest_var, prec_program_3_highest_var]
  repeat rw [Nat.max_self]

theorem execution_from_state_prec_program_1_1 (v : VectNat (n + 1)) :
    execution_from_state (0 :: v.toList ++ 0 :: List.zeros (offset_pr f_h g_h - (n + 2)) ++  0 :: List.zeros n)
      (store_X_1_to_X_succ_n (offset_pr f_h g_h + 1) n)
      = 0 :: v.toList ++ 0 :: List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  let c := offset_pr f_h g_h - (n + 2)
  have : offset_pr f_h g_h + 1 = c + n + 3 := by
    rw [Nat.succ_inj, Nat.add_assoc]
    rw [Nat.sub_add_cancel (n_plus_two_le_offset_pr f_h g_h)]
  rw [this]
  let w := 0 :: List.zeros c
  have l := lemma_store (c + 1) n ⟨w, by simp [w]⟩ v
  have : n + (c + 1) + 2 = c + n + 3 := by simp_arith
  dsimp [w] at l
  rw [this, List.zeros_succ] at l
  repeat rw [←List.cons_append] at l
  rw [l]

theorem execution_from_state_prec_program_1_2 (v : VectNat (n + 1)) :
    execution_from_state (0 :: v.toList ++ 0 :: List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList) (clear_X_j_to_X_n_plus_j 1 n)
      = 0 :: List.zeros (n + 1) ++ 0 :: List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  have : highest_var (clear_X_j_to_X_n_plus_j 1 n) + 1 ≤ (0 :: v.toList).length := by
    simp only [List.length, v.toList_length]
    rw [highest_var_clear]
  rw [List.append_assoc]
  rw [execution_from_state_gt_highest_append_list this]
  rw [clear_X_1_lemma, ←List.append_assoc]

theorem execution_from_state_prec_program_1_3 (v : VectNat (n + 1)) :
    execution_from_state (0 :: List.zeros (n + 1) ++ 0 :: List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList)
      (match n with | 0 => p_f | n + 1 => setup_X_j_to_X_n_plus_j (offset_pr f_h g_h + 1) 1 n ++ p_f)
      = f v.tail :: v.tail.toList ++ 0 :: 0 :: List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  cases n
  case zero =>
    dsimp
    repeat rw [←List.cons_append]
    rw [←List.zeros_succ, ←List.zeros_succ]
    rw [Nat.sub_add_cancel (n_plus_two_le_offset_pr f_h g_h)]
    have : 0 :: List.zeros (offset_pr f_h g_h) = [0] ++ List.zeros (offset_pr f_h g_h) := rfl
    rw [this]
    erw [←@init_state_eq 0 Vector.nil]
    rw [cleanly_computable_append_zeros_append_xs f_h _ _ (highest_var_p_f_le_offset_pr f_h g_h)]
    simp

  case succ n =>
    let ⟨x :: xs, xs_l⟩ := v
    simp at xs_l
    dsimp [-List.cons_append]
    simp only [concat_eq_seq_execution, execution_from_state, Vector.tail]
    rw [List.zeros_concat, ←List.cons_append, List.append_assoc _ [0]]
    rw [List.append_cons, List.append_assoc _ _ [x]]
    have : n + (offset_pr f_h g_h - n) + 1 = offset_pr f_h g_h + 1 := by
      have := Nat.le_trans ((Nat.le_refl n).step.step.step) (n_plus_two_le_offset_pr f_h g_h)
      rw [Nat.succ_inj, Nat.add_comm, Nat.sub_add_cancel this]
    rw [←this]
    have : ([0] ++ 0 :: List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ [x]).length
        = offset_pr f_h g_h - n := by
      simp
      rw [Nat.add_assoc n, Nat.sub_add_eq, Nat.sub_add_eq]
      have := Nat.sub_le_sub_right (n_plus_two_le_offset_pr f_h g_h) n
      rw [Nat.add_assoc, Nat.add_comm, Nat.add_sub_cancel] at this
      exact Nat.sub_add_cancel this
    erw [lemma_setup_X_1 (offset_pr f_h g_h - n) n ⟨_, this⟩ ⟨xs, xs_l⟩]
    dsimp [-List.append_assoc, -List.cons_append]
    have : 0 :: 0 :: List.zeros (offset_pr f_h g_h - (n + 1 + 2))
        = List.zeros (offset_pr f_h g_h - (n + 1)) := by
      rw [←List.zeros_succ, ←List.zeros_succ]
      simp
      exact Nat.sub_add_cancel (offset_pr_minus_n f_h g_h)
    rw [this, ←List.append_assoc, List.append_assoc _ [x]]
    erw [←@init_state_eq _ ⟨xs, xs_l⟩]
    rw [cleanly_computable_append_zeros_append_xs f_h _ _
      (Nat.sub_le_sub_right (highest_var_p_f_le_offset_pr f_h g_h) (n + 1))]
    rfl

theorem execution_from_state_prec_program_1 (v : VectNat (n + 1)) :
    execution_from_state (0 :: v.toList ++ 0 :: List.zeros (offset_pr f_h g_h - (n + 2)) ++ 0 :: List.zeros n) (prec_program_1 f_h g_h)
      = f v.tail :: v.tail.toList ++ 0 :: 0 :: List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  let p_1_1 := store_X_1_to_X_succ_n (offset_pr f_h g_h + 1) n
  let p_1_2 := clear_X_j_to_X_n_plus_j 1 n
  let p_1_3 := match n with
    | 0 => p_f
    | n + 1 => setup_X_j_to_X_n_plus_j (offset_pr f_h g_h + 1) 1 n ++ p_f
  have : prec_program_1 f_h g_h = p_1_1 ++ p_1_2 ++ p_1_3:= by
    dsimp [prec_program_1, p_1_1, p_1_2, p_1_3]

  rw [this]
  repeat rw [concat_eq_seq_execution]
  simp only [execution_from_state]
  dsimp only [p_1_1, p_1_2, p_1_3]
  rw [execution_from_state_prec_program_1_1, execution_from_state_prec_program_1_2,
    execution_from_state_prec_program_1_3]

theorem execution_from_state_prec_program_2_1 (R k : Nat) (v : VectNat (n + 1)) :
    execution_from_state (R :: k :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList) (X 2 += X 0)
      = R :: k :: R :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  exact calc
      execution_from_state (R :: k :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList) (X 2 += X 0)
    = execution_from_state ([R, k] ++ 0 :: (v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList)) (X 2 += X 0) := by simp
  _ = R :: k :: R :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
      have : [R, k].length = 2 := rfl
      rw [inc_X_i_X_j_adds_value this]
      simp [value_at]

theorem execution_from_state_prec_program_2_2 (R k : Nat) (v : VectNat (n + 1)) :
    execution_from_state (R :: k :: R :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList) (CLEAR X 0)
      = 0 :: k :: R :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  simp [execution_from_state, clear_value]

theorem execution_from_state_prec_program_2_3 (R k : Nat) (v : VectNat (n + 1)) :
    execution_from_state (0 :: k :: R :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList) p_g
      = g (k ::ᵥ R ::ᵥ v.tail) :: k :: R :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList :=
    cleanly_computable_append_zeros_append_xs g_h v.toList (k ::ᵥ R ::ᵥ v.tail)
      (Nat.sub_le_sub_right (highest_var_p_g_le_offset_pr f_h g_h) (n + 2))

theorem execution_from_state_prec_program_2_4 (R k : Nat) (v : VectNat (n + 1)) :
    execution_from_state (g (k ::ᵥ R ::ᵥ v.tail) :: k :: R :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList) (CLEAR X 2)
      = g (k ::ᵥ R ::ᵥ v.tail) :: k :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  simp [execution_from_state, clear_value]

theorem execution_from_state_prec_program_2_5 (R k : Nat) (v : VectNat (n + 1)) :
    execution_from_state (g (k ::ᵥ R ::ᵥ v.tail) :: k :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList) (INC X 1)
      = g (k ::ᵥ R ::ᵥ v.tail) :: (k + 1) :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  simp [execution_from_state, inc_value]

theorem execution_from_state_prec_program_loop_inner (R k : Nat) (v : VectNat (n + 1)) :
  execution_from_state (R :: k :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList)
    (X 2 += X 0 ++ CLEAR X 0 ++ p_g ++ CLEAR X 2 ++ INC X 1)
      = g (k ::ᵥ R ::ᵥ v.tail) :: (k + 1) :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  repeat rw [concat_eq_seq_execution]
  repeat rw [seq_execution_unfold]
  rw [execution_from_state_prec_program_2_1, execution_from_state_prec_program_2_2,
    execution_from_state_prec_program_2_3, execution_from_state_prec_program_2_4,
      execution_from_state_prec_program_2_5]

theorem execution_from_state_prec_program_loop (v : VectNat (n + 1)) :
  execution_from_state (f v.tail :: 0 :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList)
      (LOOP X (offset_pr f_h g_h + 1) DO (X 2 += X 0 ++ CLEAR X 0 ++ p_g ++ CLEAR X 2 ++ INC X 1) END)
    = (v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) :: v.head :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  let ⟨x :: xs, xs_l⟩ := v

  simp at xs_l
  dsimp [Vector.tail, Vector.head]
  simp only [execution_from_state]
  have := calc
          value_at (f ⟨xs, xs_l⟩ :: 0 :: 0 :: (xs ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ x :: xs)) (offset_pr f_h g_h + 1)
        = value_at ((f ⟨xs, xs_l⟩ :: 0 :: 0 :: xs ++ List.zeros (offset_pr f_h g_h - (n + 2))) ++ x :: xs) (offset_pr f_h g_h + 1) := rfl
      _ = x := by
          apply value_at_n
          simp [xs_l]
          rw [Nat.add_assoc, Nat.add_comm _ 2, ←Nat.add_assoc, Nat.add_comm, Nat.add_comm 2 n]
          exact Nat.sub_add_cancel (n_plus_two_le_offset_pr f_h g_h)

  rw [this]

  suffices h : ∀ k : Nat, loop_n_times k (f ⟨xs, xs_l⟩ :: 0 :: 0 :: (xs ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ x :: xs))
      (X 2 += X 0 ++ CLEAR X 0 ++ p_g ++ CLEAR X 2 ++ INC X 1)
      = Nat.rec (f ⟨xs, xs_l⟩) (fun y IH ↦ g (y ::ᵥ IH ::ᵥ ⟨xs, xs_l⟩)) k :: k :: 0 :: (xs ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ x :: xs) from h x
  intro k
  induction k
  case zero => simp [loop_n_times]
  case succ k k_ih =>
    rw [loop_n_times_loop, k_ih]
    erw [execution_from_state_prec_program_loop_inner _ _ _ _ ⟨_ :: xs, by simp [xs_l]⟩]
    rfl

theorem execution_from_state_prec_program_2 (v : VectNat (n + 1)) :
    execution_from_state (f v.tail :: v.tail.toList ++ 0 :: 0 :: List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList) (prec_program_2 f_h g_h)
      = (v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) :: v.head :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  dsimp [prec_program_2]
  cases n
  case zero =>
    simp
    have := execution_from_state_prec_program_loop f_h g_h v
    simp at this
    rw [this]

  case succ n =>
    dsimp
    repeat rw [concat_eq_seq_execution]
    repeat rw [seq_execution_unfold]
    suffices h : execution_from_state
      (execution_from_state (f v.tail ::
      (v.tail.toList ++ 0 :: 0 :: List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ v.toList))
        (clear_X_j_to_X_n_plus_j 1 n))
          (setup_X_j_to_X_n_plus_j (offset_pr f_h g_h + 1) 3 n)
        = f v.tail :: 0 :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ v.toList from by
      erw [h, execution_from_state_prec_program_loop f_h g_h v]
      rfl
    let ⟨x :: xs, xs_l⟩ := v
    simp at xs_l
    dsimp [Vector.tail]
    have := calc
        execution_from_state (f ⟨xs, xs_l⟩ :: (xs ++ 0 :: 0 :: List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ x :: xs))
          (clear_X_j_to_X_n_plus_j 1 n)
        = execution_from_state ((f ⟨xs, xs_l⟩ :: xs) ++ (0 :: 0 :: List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ x :: xs))
         (clear_X_j_to_X_n_plus_j 1 n) := by simp
      _ = (execution_from_state (f ⟨xs, xs_l⟩ :: xs) (clear_X_j_to_X_n_plus_j 1 n))
        ++ 0 :: 0 :: List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ x :: xs := by
          rw [execution_from_state_gt_highest_append_list (by rw [highest_var_clear, List.length, xs_l])]; simp
      _ = f ⟨xs, xs_l⟩ :: List.zeros (n + 1) ++ 0 :: 0 :: List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ x :: xs := by erw [clear_X_succ, clear_X_lemma ⟨xs, xs_l⟩]
      _ = f ⟨xs, xs_l⟩ ::(List.zeros (n + 1) ++ [0] ++ [0]) ++ List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ x :: xs := by simp
      _ = f ⟨xs, xs_l⟩ :: List.zeros (n + 3) ++ List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ x :: xs := by rw [←List.zeros_concat, ←List.zeros_concat]
      _ = f ⟨xs, xs_l⟩ ::  0 :: 0 :: List.zeros (n + 1) ++ List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ x :: xs := by rw [List.zeros_succ, List.zeros_succ]
      _ = f ⟨xs, xs_l⟩ ::  (0 :: (0 :: (List.zeros (n + 1) ++ List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ [x] ++ xs))) := by simp
      _ = f ⟨xs, xs_l⟩ ::  (0 :: (0 :: (List.zeros (n + 1) ++ (List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ [x]) ++ xs))) := by repeat rw [List.append_assoc]

    rw [this]
    have : offset_pr f_h g_h + 1 = (offset_pr f_h g_h - 2) + 3 := by
      erw [←@Nat.sub_add_cancel (offset_pr f_h g_h) 2 (by simp [offset_pr])]; rfl
    rw [this]
    repeat rw [setup_X_succ]
    have : n + (offset_pr f_h g_h - (n + 1 + 2) + 1) = offset_pr f_h g_h - 2 := by
      rw [Nat.add_comm (n + 1), Nat.add_comm, Nat.add_assoc, Nat.add_comm 1 n, Nat.sub_add_eq]
      erw [Nat.sub_add_cancel (Nat.sub_le_sub_right (n_plus_two_le_offset_pr f_h g_h) 2)]
    rw [←this]
    erw [lemma_setup (offset_pr f_h g_h - (n + 1 + 2) + 1) n
      ⟨List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ [x], by simp⟩ ⟨xs, xs_l⟩]
    simp

theorem execution_from_state_prec_program_3_1 (R : Nat) (v : VectNat (n + 1)) :
    execution_from_state (R :: v.head :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList)
      (match (generalizing := false) n with | 0 => CLEAR X 1 | n + 1 => CLEAR X 1 ++ clear_X_j_to_X_n_plus_j 3 n)
        = R :: 0 :: 0 :: List.zeros n ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  cases n
  case zero =>
    simp [execution_from_state, clear_value]
  case succ n =>
    simp [concat_eq_seq_execution, execution_from_state, clear_value]
    repeat rw [←List.append_assoc]
    repeat rw [clear_X_succ]
    rw [List.append_assoc]
    rw [execution_from_state_gt_highest_append_vector v.tail (by simp [highest_var_clear])]
    rw [clear_X_lemma]
    rw [←List.append_assoc]
    rw [append_zeros_addition (n + 1) ((offset_pr f_h g_h - (n + 1 + 2))) ((n + 1 + (offset_pr f_h g_h - (n + 1 + 2)))) (by simp)]

theorem execution_from_state_prec_program_3_2 (R : Nat) (v : VectNat (n + 1)) :
    execution_from_state (R :: 0 :: 0 :: List.zeros n ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList)
      (setup_X_j_to_X_n_plus_j (offset_pr f_h g_h) 1 n)
        = R :: v.toList ++ List.zeros (offset_pr f_h g_h - (n + 1)) ++ v.toList := by
  have h_eq : offset_pr f_h g_h = offset_pr f_h g_h - 1 + 1 := by
    have : offset_pr f_h g_h ≥ 1 := by simp [offset_pr]
    exact (Nat.sub_add_cancel this).symm
  rw [h_eq]
  repeat rw [List.cons_append]
  rw [setup_X_succ]
  repeat rw [←List.cons_append]
  rw [←List.zeros_succ, ←List.zeros_succ, List.zeros_concat, h_eq.symm]
  -- TODO: simplify without cons append
  simp
  rw [←List.cons_append, ←List.zeros_succ]
  have : offset_pr f_h g_h - (n + 2) + 1 = offset_pr f_h g_h - (n + 1) := by
    have : n + 2 = (n + 1) + 1 := rfl
    rw [this, Nat.sub_add_eq]
    have := Nat.sub_le_sub_right (n_plus_two_le_offset_pr f_h g_h) (n + 1)
    have h : n + 2 - (n + 1) = 1 := by simp_arith
    rw [h] at this
    exact Nat.sub_add_cancel this
  rw [this]
  -- TODO: attepm to rewrite without rewriting at h_l
  have h_l := lemma_setup (offset_pr f_h g_h - (n + 1)) n ⟨List.zeros (offset_pr f_h g_h - (n + 1)), by simp⟩ v
  have : n + (offset_pr f_h g_h - (n + 1)) = offset_pr f_h g_h - 1 := by
    rw [Nat.add_comm n 1]
    rw [Nat.add_comm, Nat.sub_add_eq]
    have : offset_pr f_h g_h ≥ n + 1 := by simp [offset_pr]
    have := Nat.sub_le_sub_right this 1
    rw [Nat.add_sub_cancel] at this
    exact Nat.sub_add_cancel this
  rw [this] at h_l
  repeat rw [List.append_assoc] at h_l
  erw [h_l]
  rfl

theorem execution_from_state_prec_program_3_3 (R : Nat) (v : VectNat (n + 1)) :
    execution_from_state (R :: v.toList ++ List.zeros (offset_pr f_h g_h - (n + 1)) ++ v.toList) (clear_Z_0_to_Z_n (offset_pr f_h g_h + 1) n)
        = R :: v.toList ++ List.zeros (offset_pr f_h g_h) := by
  have h : offset_pr f_h g_h ≥ n + 1 := by simp_arith [offset_pr]
  have : (R :: v.toList ++ List.zeros (offset_pr f_h g_h - (n + 1))).length = offset_pr f_h g_h + 1 := by
    simp
    rw [Nat.add_comm]
    exact Nat.sub_add_cancel h
  rw [clear_Z_lemma v this]
  simp
  exact Nat.sub_add_cancel h

theorem execution_from_state_prec_program_3 (v : VectNat (n + 1)) :
  execution_from_state ((v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) :: v.head :: 0 :: v.tail.toList
    ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList)
    (prec_program_3 f_h g_h)
      = (v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) :: v.toList ++ List.zeros (offset_pr f_h g_h) := by
  dsimp [prec_program_3]
  repeat rw [concat_eq_seq_execution]
  simp [execution_from_state, ←List.cons_append, -List.append_assoc]
  rw [execution_from_state_prec_program_3_1, execution_from_state_prec_program_3_2,
    execution_from_state_prec_program_3_3]

theorem execution_from_state_prec_program (v : VectNat (n + 1)) :
    execution_from_state (0 :: v.toList ++ 0 :: List.zeros (offset_pr f_h g_h - (n + 2)) ++ 0 :: List.zeros n) (prec_program f_h g_h)
      = (v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) :: v.toList ++ List.zeros (offset_pr f_h g_h) := by
  dsimp [prec_program]
  repeat rw [concat_eq_seq_execution]
  simp [execution_from_state, ←List.cons_append, -List.append_assoc]
  rw [execution_from_state_prec_program_1, execution_from_state_prec_program_2,
   execution_from_state_prec_program_3]

theorem prec_is_loop_computable_cleanly : loop_computable_cleanly f
    → loop_computable_cleanly g
    → loop_computable_cleanly fun v : VectNat (n + 1) =>
      v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail) := by
  intro ⟨p_f, f_h⟩ ⟨p_g, g_h⟩
  exists prec_program f_h g_h
  intro v
  rw [prec_program_highest_var]
  have : offset_pr f_h g_h + 1 + n - (n + 1) = offset_pr f_h g_h := by
    rw [Nat.add_assoc, Nat.add_comm 1 n]
    rw [Nat.add_sub_cancel]
  rw [this]
  have : offset_pr f_h g_h = offset_pr f_h g_h - (n + 2) + (n + 1) + 1 := by
    rw [Nat.add_assoc]
    have : offset_pr f_h g_h ≥ n + 2 := by simp [offset_pr]
    exact (Nat.sub_add_cancel this).symm
  have : init_state v ++ List.zeros (offset_pr f_h g_h)
      = 0 :: v.toList ++ 0 :: List.zeros (offset_pr f_h g_h - (n + 2)) ++ 0 :: List.zeros n := by
    dsimp [init_state]
    rw [this]
    rw [List.zeros_succ]
    rw [←append_zeros_addition (offset_pr f_h g_h - (n + 2)) (n + 1) (offset_pr f_h g_h - (n + 2) + (n + 1)) rfl]
    rw [List.zeros_succ]
    simp
  rw [this]
  rw [execution_from_state_prec_program]

end prec_is_loop_computable_cleanly_proof

section comp_is_loop_computable_cleanly_proof

-- We introduce a section as to delimit the proof, but there won't be any
-- variable declaration, to make everything more explicit.

def highest_var_p_g {n : Nat} (p_g : Fin n → Program) : Nat := match n with
  | 0 => 0
  | _ + 1 => max (highest_var (p_g 0)) (highest_var_p_g (fun i => p_g i.succ))

-- -- A bit different from offset_prec. It needs to know m, n, p_g and p_f. It
-- -- takes three explicit arguments: m, p_f and p_g (from which n is obtained).
def offset_comp (m : Nat) (p_g : Fin n → Program) (p_f : Program) : Nat
  := max (max n m) (max (highest_var p_f) (highest_var_p_g p_g))

theorem highest_var_p_g_ge_highest_var_p_g_i {p_g : Fin n → Program} :
    ∀ i : Fin n, highest_var (p_g i) ≤ highest_var_p_g p_g := by
  induction n
  case zero => intro ⟨_, _⟩; contradiction
  case succ n n_ih =>
    intro ⟨k, p⟩
    have : highest_var_p_g p_g = max (highest_var (p_g 0)) (highest_var_p_g (fun i => p_g i.succ)) := rfl
    rw [this]
    cases (Nat.decEq k 0)
    case isTrue h => simp [h]
    case isFalse h =>
      suffices h' : highest_var (p_g ⟨k, p⟩) ≤ highest_var_p_g (fun i => p_g i.succ) from by simp [h']
      have := (Nat.succ_pred h).symm
      have p' : k - 1 < n := by rw [this] at p; exact Nat.lt_of_succ_lt_succ p
      have : (p_g ⟨k, p⟩) = (fun i : Fin n => p_g i.succ) ⟨k - 1, p'⟩ := by
        apply congrArg
        exact Fin.eq_of_val_eq this
      rw [this]
      exact @n_ih (fun i : Fin n => p_g i.succ) ⟨k - 1, p'⟩

theorem n_le_offset_comp (m : Nat) (p_g : Fin n → Program) (p_f : Program) :
  n ≤ offset_comp m p_g p_f := by simp [offset_comp]

theorem m_le_offset_comp (m : Nat) (p_g : Fin n → Program) (p_f : Program) :
  m ≤ offset_comp m p_g p_f := by simp [offset_comp]

theorem highest_var_p_f_le_offset_comp (m : Nat) (p_g : Fin n → Program) (p_f : Program) :
  highest_var p_f ≤ offset_comp m p_g p_f := by simp [offset_comp]

theorem highest_var_p_g_le_offset_comp (m : Nat) (p_g : Fin n → Program) (p_f : Program) :
  highest_var_p_g p_g  ≤ offset_comp m p_g p_f := by simp [offset_comp]

def execution_from_state_comp_store_succ_m_inputs (m : Nat) (p_g : Fin n → Program) (p_f : Program) (v : VectNat (m + 1)) :
    execution_from_state (0 :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ List.zeros (((m + 1) + n)))
    (store_X_1_to_X_succ_n (offset_comp (m + 1) p_g p_f + 1) m)
      = 0 :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ v.toList ++ List.zeros n := by
  rw [←append_zeros_addition (m + 1) n ((m + 1) + n) rfl, ←List.append_assoc]
  have h : offset_comp (m + 1) p_g p_f - (m + 1) + (m + 1) = offset_comp (m + 1) p_g p_f := by
    exact Nat.sub_add_cancel (m_le_offset_comp (m + 1) p_g p_f)
  exact calc
    execution_from_state (0 :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ List.zeros (m + 1) ++ List.zeros n)
      (store_X_1_to_X_succ_n (offset_comp (m + 1) p_g p_f + 1) m)
        =
    execution_from_state ((0 :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ List.zeros (m + 1)) ++ List.zeros n)
      (store_X_1_to_X_succ_n (offset_comp (m + 1) p_g p_f + 1) m)
      := by rfl
      _ =
    (execution_from_state (0 :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ List.zeros (m + 1))
      (store_X_1_to_X_succ_n (offset_comp (m + 1) p_g p_f + 1) m)) ++ List.zeros n
      := by
          erw [execution_from_state_gt_highest_append_vector
             ⟨_, by simp; rw [h]⟩ (by simp_arith [highest_var_store])]
          rfl
      _ =
    0 :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ v.toList ++ List.zeros n
      := by
          have : (m + (offset_comp (m + 1) p_g p_f - (m + 1)) + 2)
            = offset_comp (m + 1) p_g p_f + 1 := by rw [←h]; simp_arith
          erw [←this, lemma_store _ m
            ⟨List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)), by simp⟩ v]
          rfl


def compute_store_g_i (p_g : Fin n → Program) (offset_store : Nat) (i : Fin n) : Program :=
  p_g i ++ (X (offset_store + 1 + i) += X 0) ++ CLEAR X 0

def compute_store_all_succ_n_g (n m : Nat) (p_g : Fin (n + 1) → Program) (p_f : Program) (offset_store : Nat) : Program :=
  match n with
  | 0 => compute_store_g_i p_g offset_store 0
  | n + 1 => compute_store_g_i p_g offset_store 0 ++ compute_store_all_succ_n_g n m (fun i => p_g i.succ) p_f (offset_store + 1)

def execution_from_state_comp_compute_store_succ_n_g (m : Nat) (g : Fin (n + 1) → VectNat m → Nat) (p_g : Fin (n + 1) → Program)
    (g_h : ∀ i, cleanly_computes (p_g i) (g i)) (p_f : Program) (v : VectNat m) :
    execution_from_state (0 :: v.toList ++ List.zeros (offset_comp m p_g p_f - m) ++ v.toList ++ List.zeros (n + 1))
    (compute_store_all_succ_n_g n m p_g p_f (offset_comp m p_g p_f + m))
      = 0 :: v.toList ++ List.zeros (offset_comp m p_g p_f - m) ++ v.toList ++ (Vector.ofFn (fun i => g i v)).toList := by

  suffices h : ∀ c s : Nat, ∀ u : VectNat s, c ≥ highest_var_p_g p_g - m →
    execution_from_state (0 :: v.toList ++ List.zeros c ++ u.toList ++ List.zeros (n + 1))
    (compute_store_all_succ_n_g n m p_g p_f (c + m + s))
      = 0 :: v.toList ++ List.zeros c ++ u.toList ++ (Vector.ofFn fun i => g i v).toList from by
    have r := h (offset_comp m p_g p_f - m) m v
      (Nat.sub_le_sub_right (highest_var_p_g_le_offset_comp m p_g p_f) m)
    rw [←r, Nat.sub_add_cancel (m_le_offset_comp m p_g p_f)]
  revert g p_g
  induction n
  case zero =>
    -- s u c_h variable
    intro g p_g g_h c s u c_h
    dsimp only [compute_store_all_succ_n_g, compute_store_g_i, concat_eq_seq_execution]
    simp [execution_from_state, -List.cons_append, -List.append_assoc]
    rw [←@init_state_eq _ v, List.append_assoc _ u.toList]
    have : c ≥ highest_var (p_g 0) - m := by
      apply Nat.le_trans (Nat.sub_le_sub_right _ m) c_h
      exact highest_var_p_g_ge_highest_var_p_g_i 0
    rw [cleanly_computable_append_zeros_append_xs (g_h 0) _ v this]
    rw [←List.append_assoc]
    rw [inc_X_i_X_j_adds_value (by simp_arith)]
    simp [clear_value, value_at_cons_zero, init_state]
  case succ n n_ih =>
    intro g p_g g_h c s u c_h
    dsimp only [compute_store_all_succ_n_g, compute_store_g_i, concat_eq_seq_execution]
    simp [execution_from_state, -List.cons_append, -List.append_assoc]
    conv => lhs; rw [←@init_state_eq _ v, List.zeros_succ]
    rw [List.append_assoc _ u.toList]
    have : c ≥ highest_var (p_g 0) - m := by
      apply Nat.le_trans (Nat.sub_le_sub_right _ m) c_h
      exact highest_var_p_g_ge_highest_var_p_g_i 0
    rw [cleanly_computable_append_zeros_append_xs (g_h 0) _ v this]
    rw [←List.append_assoc]
    rw [inc_X_i_X_j_adds_value (by simp_arith)]
    simp [clear_value, value_at_cons_zero, init_state]
    have : g 0 v :: List.zeros (n + 1) = [g 0 v] ++ List.zeros (n + 1) := rfl
    rw [this]
    repeat rw [←List.append_assoc]
    repeat rw [←List.cons_append]
    rw [List.append_assoc _ u.toList]
    let u' : VectNat (s + 1) := ⟨u.toList ++ [g 0 v], by simp⟩
    have : u.toList ++ [g 0 v] = u'.toList := rfl
    rw [this, Nat.add_assoc, n_ih _ _ (by intro i; exact g_h i.succ) _ _ _
      (by apply Nat.le_trans (Nat.sub_le_sub_right _ m) c_h; simp [highest_var_p_g])]
    simp [u']

def execution_from_state_comp_clear_succ_m_inputs (m : Nat) (p_g : Fin n → Program) (p_f : Program) (v : VectNat (m + 1)) :
    execution_from_state (0 :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ v.toList ++ xs)
      (clear_X_j_to_X_n_plus_j 1 m)
        = 0 :: List.zeros (offset_comp (m + 1) p_g p_f) ++ v.toList ++ xs := by
  repeat rw [List.cons_append]
  rw [clear_X_succ]
  repeat rw [List.append_assoc]
  rw [execution_from_state_gt_highest_append_vector v (by rw [highest_var_clear]; rfl)]
  rw [clear_X_lemma]
  repeat rw [←List.append_assoc]
  rw [append_zeros_addition (m + 1) (offset_comp (m + 1) p_g p_f - (m + 1)) (offset_comp (m + 1) p_g p_f)]
  rw [Nat.add_comm]
  apply Nat.sub_add_cancel
  exact m_le_offset_comp (m + 1) p_g p_f

def execution_from_state_comp_setup_succ_n_inputs (m : Nat) (g : Fin (n + 1) → VectNat m → Nat) (p_g : Fin (n + 1) → Program)
    (p_f : Program) (v : VectNat m) :
    execution_from_state (0 :: List.zeros (offset_comp m p_g p_f) ++ v.toList ++ (Vector.ofFn (fun i => g i v)).toList)
    (setup_X_j_to_X_n_plus_j (offset_comp m p_g p_f + m) 1 n)
      = 0 :: (Vector.ofFn (fun i => g i v)).toList ++ List.zeros (offset_comp m p_g p_f - (n + 1)) ++ v.toList ++ (Vector.ofFn (fun i => g i v)).toList := by
  generalize Vector.ofFn (fun i => g i v) = w

  have : offset_comp m p_g p_f + m ≥ 1 := Nat.le_add_right_of_le (by simp_arith [offset_comp])
  rw [←Nat.sub_add_cancel this]
  conv => lhs; repeat rw [List.cons_append]
  rw [setup_X_succ]

  have h : offset_comp m p_g p_f ≥ n + 1 := by simp_arith [offset_comp]
  conv =>
    lhs
    congr
    rfl
    congr
    rw [←Nat.sub_add_cancel h]
    rw [Nat.add_comm]
    rw [←append_zeros_addition _ _ _ rfl]
    rw [List.append_assoc _ _ v.toList]

  have : (n + (m + offset_comp m p_g p_f - (n + 1))) = offset_comp m p_g p_f + m - 1 := by
    conv =>
      lhs
      rw [Nat.add_sub_assoc h _]
      rw [Nat.add_comm, Nat.add_assoc]
      rw [←Nat.add_sub_cancel (offset_comp m p_g p_f - (n + 1) + n) 1]
      rw [Nat.add_assoc, Nat.sub_add_cancel h]
      rw [←Nat.add_sub_assoc (Nat.le_trans (by simp) h) m]
      rw [Nat.add_comm]
  rw [←this]
  erw [lemma_setup _ _
    ⟨List.zeros (offset_comp m p_g p_f - (n + 1)) ++ Vector.toList v,
      by simp; rw [Nat.add_comm, ←Nat.add_sub_assoc h]⟩ w]
  simp

def execution_from_state_comp_clear_succ_n_z (m : Nat) (g : Fin (n + 1) → VectNat m → Nat) (p_g : Fin (n + 1) → Program)
    (p_f : Program) (v : VectNat m) :
    execution_from_state (0 :: (Vector.ofFn (fun i => g i v)).toList ++ List.zeros (offset_comp m p_g p_f - (n + 1)) ++ v.toList
      ++ (Vector.ofFn (fun i => g i v)).toList) (clear_Z_0_to_Z_n (offset_comp m p_g p_f + m + 1) n)
      = 0 :: (Vector.ofFn (fun i => g i v)).toList ++ List.zeros (offset_comp m p_g p_f - (n + 1)) ++ v.toList ++ List.zeros (n + 1) := by
  generalize Vector.ofFn (fun i => g i v) = w
  have : (0 :: w.toList ++ List.zeros (offset_comp m p_g p_f - (n + 1)) ++ Vector.toList v).length
      = offset_comp m p_g p_f + m + 1 := by
    simp
    rw [Nat.add_comm _ m, Nat.add_comm, Nat.add_assoc, Nat.add_comm _ m]
    simp_arith
    rw [Nat.add_assoc]
    exact Nat.sub_add_cancel (n_le_offset_comp m p_g p_f)
  rw [clear_Z_lemma w this]

def execution_from_state_comp_execute_p_f (g : Fin n → VectNat m → Nat) (p_g : Fin n → Program)
    (f_h : cleanly_computes p_f f) :
    execution_from_state (0 :: (Vector.ofFn (fun i => g i v)).toList ++ List.zeros (offset_comp m p_g p_f - n) ++ v.toList ++ List.zeros n)
      p_f =  f (Vector.ofFn (fun i => g i v)) :: (Vector.ofFn (fun i => g i v)).toList ++ List.zeros (offset_comp m p_g p_f - n) ++ v.toList ++ List.zeros n := by
  generalize Vector.ofFn (fun i => g i v) = w
  rw [List.append_assoc _ v.toList]
  erw [cleanly_computable_append_zeros_append_xs f_h (v.toList ++ List.zeros n) w
    (Nat.sub_le_sub_right (highest_var_p_f_le_offset_comp m p_g p_f) _)]
  rw [←List.append_assoc]

def execution_from_state_comp_clear_succ_n_inputs (m : Nat) (g : Fin (n + 1) → VectNat m → Nat) (p_g : Fin (n + 1) → Program)
    (p_f : Program) (v : VectNat m) :
    execution_from_state (x :: (Vector.ofFn (fun i => g i v)).toList ++ List.zeros (offset_comp m p_g p_f - (n + 1))
      ++ v.toList ++ List.zeros (n + 1)) (clear_X_j_to_X_n_plus_j 1 n)
      = x :: List.zeros (offset_comp m p_g p_f) ++ v.toList ++ List.zeros (n + 1) := by
  generalize Vector.ofFn (fun i => g i v) = w
  repeat rw [List.append_assoc]
  repeat rw [List.cons_append]
  rw [clear_X_succ]
  rw [execution_from_state_gt_highest_append_vector w (by simp_arith [highest_var_clear])]
  rw [clear_X_lemma]
  simp [←List.append_assoc]
  rw [Nat.add_comm]
  exact Nat.sub_add_cancel (n_le_offset_comp m p_g p_f)

def execution_from_state_comp_setup_succ_m_inputs (m : Nat) (p_g : Fin n → Program) (p_f : Program) (v : VectNat (m + 1)) :
    execution_from_state (x :: List.zeros (offset_comp (m + 1) p_g p_f) ++ v.toList ++ List.zeros n)
    (setup_X_j_to_X_n_plus_j (offset_comp (m + 1) p_g p_f) 1 m)
      = x :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ v.toList ++ List.zeros n := by
  exact calc
    execution_from_state (x :: List.zeros (offset_comp (m + 1) p_g p_f) ++ v.toList ++ List.zeros n)
      (setup_X_j_to_X_n_plus_j (offset_comp (m + 1) p_g p_f) 1 m)
      =
    execution_from_state (x :: List.zeros (offset_comp (m + 1) p_g p_f) ++ v.toList)
      (setup_X_j_to_X_n_plus_j (offset_comp (m + 1) p_g p_f) 1 m) ++ List.zeros n
        := by
            have : offset_comp (m + 1) p_g p_f + (m + 1)
              ≥ highest_var (setup_X_j_to_X_n_plus_j (offset_comp (m + 1) p_g p_f) 1 m) := by
                rw [highest_var_setup, Nat.add_assoc]
                rw [Nat.max_eq_right (Nat.le_add_left _ _)]
            erw [execution_from_state_gt_highest_append_vector
              ⟨x :: List.zeros (offset_comp (m + 1) p_g p_f) ++ v.toList, by simp⟩ this]
            rfl
    _ =
    execution_from_state (x :: (List.zeros (offset_comp (m + 1) p_g p_f) ++ v.toList))
      (setup_X_j_to_X_n_plus_j (offset_comp (m + 1) p_g p_f) 1 m) ++ List.zeros n
        := rfl
    _ =
      x :: execution_from_state (List.zeros (offset_comp (m + 1) p_g p_f) ++ v.toList)
      (setup_X_j_to_X_n_plus_j (offset_comp (m + 1) p_g p_f - 1) 0 m) ++ List.zeros n
        := by
            have : offset_comp (m + 1) p_g p_f = offset_comp (m + 1) p_g p_f - 1 + 1 := by
              suffices h : offset_comp (m + 1) p_g p_f ≥ 1 from (Nat.sub_add_cancel h).symm
              simp_arith [offset_comp]
            rw [this, setup_X_succ]
            rfl
    _ =
      x :: execution_from_state (List.zeros (m + 1) ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ v.toList)
      (setup_X_j_to_X_n_plus_j (offset_comp (m + 1) p_g p_f - 1) 0 m) ++ List.zeros n
        := by
            rw [←append_zeros_addition (m + 1) (offset_comp (m + 1) p_g p_f - (m + 1))
              (offset_comp (m + 1) p_g p_f)]
            rw [Nat.add_comm, Nat.sub_add_cancel]
            exact m_le_offset_comp (m + 1) p_g p_f
    _ =
      x :: (v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ v.toList)
       ++ List.zeros n
        := by
            have : m + (offset_comp (m + 1) p_g p_f - (m + 1)) = offset_comp (m + 1) p_g p_f - 1 := by
              rw [Nat.add_comm m]
              have h : ∀ a : Nat, offset_comp (m + 1) p_g p_f - (m + 1) + a
                  = offset_comp (m + 1) p_g p_f - (m + 1) + (a + 1) - 1 := by intros; simp_arith
              rw [h m]
              suffices h : (m + 1) ≤ offset_comp (m + 1) p_g p_f from congrArg (· - 1) (Nat.sub_add_cancel h)
              simp_arith [offset_comp]
            erw [←this, lemma_setup _ m
              ⟨List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)), by simp⟩ v]
            rfl
    _ =
    x :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ v.toList ++ List.zeros n
        := rfl

def execution_from_state_comp_clear_succ_m_z (m : Nat) (p_g : Fin n → Program) (p_f : Program) (v : VectNat (m + 1)) :
    execution_from_state (x :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ v.toList ++ List.zeros n)
    (clear_Z_0_to_Z_n (offset_comp (m + 1) p_g p_f + 1) m)
      = x :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ List.zeros ((m + 1) + n) := by
  calc
    execution_from_state (x :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ v.toList ++ List.zeros n)
      (clear_Z_0_to_Z_n (offset_comp (m + 1) p_g p_f + 1) m)
      =
    execution_from_state ((x :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ v.toList) ++ List.zeros n)
      (clear_Z_0_to_Z_n (offset_comp (m + 1) p_g p_f + 1) m)
        := rfl
    _ =
    execution_from_state (x :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ v.toList)
      (clear_Z_0_to_Z_n (offset_comp (m + 1) p_g p_f + 1) m) ++ List.zeros n
        := by
          have h : (x :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ v.toList).length
              = offset_comp (m + 1) p_g p_f + (m + 1) + 1 := by
            simp
            rw [Nat.add_comm]
            apply Nat.add_right_cancel_iff.mpr
            rw [Nat.sub_add_cancel (m_le_offset_comp (m + 1) p_g p_f)]
          erw [execution_from_state_gt_highest_append_vector
            ⟨_, h⟩ (by rw [highest_var_clear_Z, Nat.add_assoc, Nat.add_comm 1 m])]
          rfl
    _ = x :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ List.zeros ((m + 1) + n)
        := by
            have : (x :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1))).length
                = offset_comp (m + 1) p_g p_f + 1 := by
              simp
              rw [Nat.add_comm]
              rw [Nat.sub_add_cancel (m_le_offset_comp (m + 1) p_g p_f)]
            rw [clear_Z_lemma v this]
            repeat rw [List.append_assoc]
            rw [append_zeros_addition (m + 1) n ((m + 1) + n) rfl]

def comp_program (g : Fin n → VectNat m → Nat) (_ : cleanly_computes p_f f) (p_g : Fin n → Program)
    (_ : ∀ i, cleanly_computes (p_g i) (g i)) : Program := match n with
  | 0 => match m with
    | 0 => p_f
    | m + 1 =>
         store_X_1_to_X_succ_n (offset_comp (m + 1) p_g p_f + 1) m
      ++ clear_X_j_to_X_n_plus_j 1 m
      ++ p_f
      ++ setup_X_j_to_X_n_plus_j (offset_comp (m + 1) p_g p_f) 1 m
      ++ clear_Z_0_to_Z_n (offset_comp (m + 1) p_g p_f + 1) m
  | n + 1 => match m with
    | 0 =>
         compute_store_all_succ_n_g n 0 p_g p_f (offset_comp 0 p_g p_f)
      ++ setup_X_j_to_X_n_plus_j (offset_comp 0 p_g p_f) 1 n
      ++ clear_Z_0_to_Z_n (offset_comp 0 p_g p_f + 1) n
      ++ p_f
      ++ clear_X_j_to_X_n_plus_j 1 n
    | m + 1 =>
         store_X_1_to_X_succ_n (offset_comp (m + 1) p_g p_f + 1) m
      ++ compute_store_all_succ_n_g n (m + 1) p_g p_f (offset_comp (m + 1) p_g p_f + (m + 1))
      ++ clear_X_j_to_X_n_plus_j 1 m
      ++ setup_X_j_to_X_n_plus_j (offset_comp (m + 1) p_g p_f + (m + 1)) 1 n
      ++ clear_Z_0_to_Z_n (offset_comp (m + 1) p_g p_f + (m + 1) + 1) n
      ++ p_f
      ++ clear_X_j_to_X_n_plus_j 1 n
      ++ setup_X_j_to_X_n_plus_j (offset_comp (m + 1) p_g p_f) 1 m
      ++ clear_Z_0_to_Z_n (offset_comp (m + 1) p_g p_f + 1) m

def offset_comp_lemma (m : Nat) (p_g : Fin (n + 1) → Program) (p_f : Program) :
    offset_comp m p_g p_f ≥ offset_comp m (fun i => p_g i.succ) p_f := by
  apply max_le_lemma (max_le_lemma (Nat.le_succ n) (Nat.le_refl m)) ?_
  apply max_le_lemma (Nat.le_refl (highest_var p_f)) ?_
  simp [highest_var_p_g]

def highest_var_compute_store_all_succ_n_g_lemma (n m k : Nat) (p_g : Fin (n + 1) → Program) (p_f : Program)
    : ∀ x : Nat, x ≥ offset_comp m p_g p_f →
      highest_var (compute_store_all_succ_n_g n m p_g p_f (x + k))
      = highest_var (compute_store_all_succ_n_g n m p_g p_f x) + k := by
  revert p_g  k
  induction n
  case zero =>
    intro k p_g x x_h
    dsimp [compute_store_all_succ_n_g, compute_store_g_i, highest_var]
    repeat rw [Nat.max_zero, Nat.zero_max]
    have : highest_var (p_g 0) ≤ highest_var_p_g p_g := highest_var_p_g_ge_highest_var_p_g_i 0
    have := Nat.le_trans this (highest_var_p_g_le_offset_comp m p_g p_f)
    have := Nat.le_trans this x_h
    rw [Nat.max_eq_right (Nat.le_add_right_of_le this)]
    rw [Nat.add_assoc]
    rw [Nat.max_eq_right (Nat.le_add_right_of_le this)]
    rw [Nat.add_comm k 1, Nat.add_assoc]
  case succ n n_ih =>
    intro k p_g x x_h
    dsimp [compute_store_all_succ_n_g, compute_store_g_i, highest_var]
    repeat rw [Nat.max_zero, Nat.zero_max]
    have : highest_var (p_g 0) ≤ highest_var_p_g p_g := highest_var_p_g_ge_highest_var_p_g_i 0
    have := Nat.le_trans (Nat.le_trans this (highest_var_p_g_le_offset_comp m p_g p_f)) x_h
    rw [Nat.max_eq_right (Nat.le_add_right_of_le this)]
    rw [Nat.add_assoc x, Nat.max_eq_right (Nat.le_add_right_of_le this)]
    rw [Nat.add_comm k 1, ←Nat.add_assoc]

    suffices h : highest_var (compute_store_all_succ_n_g n m (fun i ↦ p_g i.succ) p_f (x + 1 + k))
        = highest_var (compute_store_all_succ_n_g n m (fun i ↦ p_g i.succ) p_f (x + 1)) + k from by
      rw [h]
      generalize highest_var (compute_store_all_succ_n_g n m (fun i ↦ p_g i.succ) p_f (x + 1)) = t
      apply Nat.add_max_add_right
    rw [Nat.add_assoc]
    have : offset_comp m (fun i => p_g i.succ) p_f ≤ x := Nat.le_trans (offset_comp_lemma _ _ _) x_h
    rw [n_ih (1 + k) (fun i => p_g i.succ) x this]
    rw [←Nat.add_assoc]
    rw [n_ih 1 (fun i => p_g i.succ) x this]


def highest_var_compute_store_all_succ_n_g (n m : Nat) (p_g : Fin (n + 1) → Program) (p_f : Program)
    : highest_var (compute_store_all_succ_n_g n m p_g p_f (offset_comp m p_g p_f + m))
      = offset_comp m p_g p_f + m + (n + 1) := by
  rw [highest_var_compute_store_all_succ_n_g_lemma _ m m p_g p_f _
    (Nat.le_refl (offset_comp m p_g p_f))]
  suffices h : ∀ x : Nat, x ≥ offset_comp m p_g p_f →
    highest_var (compute_store_all_succ_n_g n m p_g p_f x)
     = x + (n + 1) from by
      rw [h (offset_comp m p_g p_f) (Nat.le_refl (offset_comp m p_g p_f))]
      simp_arith
  revert p_g
  induction n
  case zero =>
    intro p_g x x_h
    dsimp [compute_store_all_succ_n_g, compute_store_g_i, highest_var]
    rw [Nat.zero_max, Nat.max_zero]
    apply Nat.max_eq_right
    apply Nat.le_add_right_of_le
    apply Nat.le_trans (@highest_var_p_g_ge_highest_var_p_g_i 1 p_g 0)
    exact Nat.le_trans (highest_var_p_g_le_offset_comp m p_g p_f) x_h

  case succ n n_ih =>
    intro p_g x x_h
    dsimp [compute_store_all_succ_n_g, highest_var]
    rw [Nat.zero_max, Nat.max_zero]
    have := Nat.le_trans (highest_var_p_g_le_offset_comp m p_g p_f) x_h
    have := Nat.le_trans (@highest_var_p_g_ge_highest_var_p_g_i _ p_g 0) this
    rw [Nat.max_eq_right (Nat.le_add_right_of_le this)]
    have : offset_comp m (fun i => p_g i.succ) p_f ≤ x := Nat.le_trans (offset_comp_lemma m p_g p_f) x_h
    rw [n_ih (fun i => p_g i.succ) (x + 1) (Nat.le_trans this (Nat.le_succ x))]
    rw [Nat.max_eq_right] <;> simp_arith

-- TODO: review
def highest_var_comp_program (g : Fin n → VectNat m → Nat) (f_h : cleanly_computes p_f f) (p_g : Fin n → Program)
    (g_h : ∀ i, cleanly_computes (p_g i) (g i)) :
      highest_var (comp_program g f_h p_g g_h) = offset_comp m p_g p_f + m + n := by
  cases n
  case zero =>
    cases m
    case zero =>
      dsimp [comp_program, offset_comp]
      rw [highest_var_p_g, Nat.max_zero, Nat.zero_max, Nat.max_zero]
    case succ m =>
      dsimp [comp_program, highest_var]
      rw [highest_var_store, highest_var_clear, highest_var_setup,
        highest_var_clear_Z]
      -- TODO: simplify
      have : max (m + 1) (offset_comp (m + 1) p_g p_f + 1 + m)
          = offset_comp (m + 1) p_g p_f + 1 + m := by
        rw [Nat.add_assoc]
        exact Nat.max_eq_right (Nat.le_add_right_of_le (m_le_offset_comp (m + 1) p_g p_f))
      rw [Nat.max_comm _ (m + 1)]
      rw [this, this]
      conv =>
        lhs
        pattern _ + m + 1
        rw [Nat.add_assoc]
        congr
        rfl
        rw [Nat.add_comm]
        rfl
      rw [←Nat.add_assoc]
      rw [this]
      -- TODO: simplify
      have : max (offset_comp (m + 1) p_g p_f + 1 + m) (highest_var p_f)
          = offset_comp (m + 1) p_g p_f + 1 + m := by
        rw [Nat.add_assoc]
        exact Nat.max_eq_left (Nat.le_add_right_of_le (highest_var_p_f_le_offset_comp (m + 1) p_g p_f))

      rw [this]
      rw [Nat.max_self, Nat.max_self, Nat.add_comm m 1, ←Nat.add_assoc]
  case succ n =>
    cases m
    case zero =>
      dsimp [comp_program, highest_var]
      rw [highest_var_setup, highest_var_clear, highest_var_clear_Z]
      have := Nat.add_zero (offset_comp 0 p_g p_f)
      rw [this.symm]
      rw [highest_var_compute_store_all_succ_n_g]
      rw [this]
      have h : max (n + 1) (offset_comp 0 p_g p_f + n + 1) = offset_comp 0 p_g p_f + n + 1 := by simp_arith
      rw [h]
      rw [←Nat.add_assoc, Nat.max_self]
      have : offset_comp 0 p_g p_f + n + 1 = offset_comp 0 p_g p_f + 1 + n:= by simp_arith
      rw [this, Nat.max_self, this.symm]
      have : max (offset_comp 0 p_g p_f + n + 1) (highest_var p_f) = offset_comp 0 p_g p_f + n + 1 := by
        have : highest_var p_f ≤ offset_comp 0 p_g p_f := by simp_arith [offset_comp]
        have := @Nat.le_add_right_of_le _  _ (n + 1) this
        rw [←Nat.add_assoc] at this
        rw [Nat.max_eq_left this]
      rw [this, Nat.max_comm, h]
    case succ m =>
      dsimp [comp_program, highest_var]
      rw [highest_var_compute_store_all_succ_n_g]
      repeat rw [highest_var_store]
      repeat rw [highest_var_clear]
      repeat rw [highest_var_clear_Z]
      repeat rw [highest_var_setup]
      rw [Nat.add_assoc, Nat.add_comm 1 m]
      rw [Nat.add_assoc _ n 1]
      rw [Nat.add_assoc _ m 1]
      have l : ∀ a b : Nat, max a (b + a) = b + a := by simp_arith
      have l' : ∀ a b : Nat, max a (a + b) = a + b := by simp_arith
      rw [l, l, l']
      rw [Nat.max_comm _ (m + 1)]
      rw [Nat.add_assoc _ (m + 1), Nat.add_comm (m + 1), ←Nat.add_assoc _ _ (m + 1)]
      rw [l, Nat.max_self]
      rw [Nat.add_assoc _ 1 n, Nat.add_comm 1 n, Nat.add_assoc _ _ (n + 1),
        Nat.add_comm (m + 1) (n + 1), ←Nat.add_assoc _ (n + 1)]
      rw [Nat.max_self]
      -- TODO: simplify
      have : max (offset_comp (m + 1) p_g p_f + (n + 1) + (m + 1)) (highest_var p_f)
          = offset_comp (m + 1) p_g p_f + (n + 1) + (m + 1) := by
        rw [Nat.add_assoc]
        exact Nat.max_eq_left (Nat.le_add_right_of_le (highest_var_p_f_le_offset_comp (m + 1) p_g p_f))
      rw [this, Nat.max_comm _ (n + 1)]
      rw [Nat.add_assoc _ (n + 1), Nat.add_comm (n + 1) _, ←Nat.add_assoc _ _ (n + 1)]
      rw [l]
      rw [Nat.max_comm (offset_comp (m + 1) p_g p_f + (m + 1) + (n + 1))]
      rw [l', Nat.max_comm, l']

theorem execution_from_state_comp (g : Fin n → VectNat m → Nat) (f_h : cleanly_computes p_f f) (p_g : Fin n → Program)
    (g_h : ∀ i, cleanly_computes (p_g i) (g i)) (v : VectNat m):
   execution_from_state (init_state v ++ List.zeros (offset_comp m p_g p_f - m) ++ List.zeros (m + n))
     (comp_program g f_h p_g g_h) =
    f (Vector.ofFn fun i => g i v) :: Vector.toList v ++ List.zeros (offset_comp m p_g p_f - m) ++ List.zeros (m + n) := by
  cases n
  · cases m
    · simp [init_state, comp_program]
      have := @execution_from_state_comp_execute_p_f _ _ p_f f v g p_g f_h
      simp at this; rw [this]
    · dsimp only [init_state, comp_program, concat_eq_seq_execution]
      simp only [execution_from_state]
      rw [execution_from_state_comp_store_succ_m_inputs]
      rw [execution_from_state_comp_clear_succ_m_inputs]
      erw [execution_from_state_comp_execute_p_f (f_h := f_h)]
      erw [execution_from_state_comp_setup_succ_m_inputs]
      rw [execution_from_state_comp_clear_succ_m_z]
  · cases m
    · dsimp only [init_state, comp_program, concat_eq_seq_execution]
      simp [execution_from_state]
      have := @execution_from_state_comp_compute_store_succ_n_g _ _ g p_g g_h p_f v
      simp at this; rw [this]
      have := @execution_from_state_comp_setup_succ_n_inputs _ _ g p_g p_f v
      simp at this; rw [this]
      have := @execution_from_state_comp_clear_succ_n_z _ _ g p_g p_f v
      simp at this; rw [this]
      have := @execution_from_state_comp_execute_p_f _ _ p_f f v g p_g f_h
      simp at this; rw [this]
      have := @execution_from_state_comp_clear_succ_n_inputs _ (f (Vector.ofFn fun i => g i v)) _ g p_g p_f v
      simp at this; rw [this]
    · dsimp only [init_state, comp_program, concat_eq_seq_execution]
      simp only [execution_from_state]
      rw [execution_from_state_comp_store_succ_m_inputs]
      rw [execution_from_state_comp_compute_store_succ_n_g (g_h := g_h)]
      rw [execution_from_state_comp_clear_succ_m_inputs]
      rw [execution_from_state_comp_setup_succ_n_inputs]
      rw [execution_from_state_comp_clear_succ_n_z]
      rw [execution_from_state_comp_execute_p_f (f_h := f_h)]
      rw [execution_from_state_comp_clear_succ_n_inputs]
      rw [execution_from_state_comp_setup_succ_m_inputs]
      rw [execution_from_state_comp_clear_succ_m_z]

theorem comp_is_loop_computable_cleanly (g : Fin n → VectNat m → Nat) :
      loop_computable_cleanly f
    → (∀ i, loop_computable_cleanly (g i))
    → loop_computable_cleanly fun a => f (Vector.ofFn fun i => g i a) := by
  intro ⟨p_f, f_h⟩ g_h
  have ⟨p_g, g_h⟩ := forall_exists_function g g_h
  exists comp_program g f_h p_g g_h
  intro v
  rw [highest_var_comp_program]
  have : offset_comp m p_g p_f + m + n - m = (offset_comp m p_g p_f - m) + (m + n) := by
    rw [Nat.add_assoc , Nat.add_comm m n, ←Nat.add_assoc]
    rw [Nat.add_sub_cancel]
    rw [Nat.add_comm n m, ←Nat.add_assoc]
    rw [Nat.sub_add_cancel (m_le_offset_comp m p_g p_f)]
  rw [this]
  simp_arith
  rw [←append_zeros_addition (offset_comp m p_g p_f - m) (m + n)
     (offset_comp m p_g p_f - m + (m + n)) rfl]
  repeat rw [←List.append_assoc]
  repeat rw [←List.cons_append]
  rw [execution_from_state_comp]

end comp_is_loop_computable_cleanly_proof


-- TODO: make program explicit
theorem primrec'_is_loop_computable_cleanly : Nat.Primrec' f → loop_computable_cleanly f := by
  intro h
  induction h
  case zero => exact zero_is_loop_computable_cleanly
  case succ => exact succ_is_loop_computable_cleanly
  case get i => exact get_is_loop_computable_cleanly i
  case comp g _ _ f_ih g_ih => exact comp_is_loop_computable_cleanly g f_ih g_ih
  case prec f_ih g_ih => exact prec_is_loop_computable_cleanly f_ih g_ih

-- TODO: make shorter
theorem primrec'_is_loop_computable {f : VectNat n → Nat} :
    Nat.Primrec' f → loop_computable f := by
  intro h
  have := primrec'_is_loop_computable_cleanly h
  have := loop_computable_cleanly_is_loop_computable this
  assumption

--

def inc_value_i_vect (m i : Nat) : Fin (m + 1) → VectNat 1 → Nat :=
  fun j z => if (i = j) then (decode_VectNat m i z).succ else decode_VectNat m j z

def clear_value_i_vect (m i : Nat) : Fin (m + 1) → VectNat 1 → Nat :=
  fun j z => if (i = j) then 0 else decode_VectNat m j z

theorem inc_value_i_vect_primrec' (m i : Nat) :
    ∀ j : Fin (m + 1), Nat.Primrec' (inc_value_i_vect m i j) := by
  intro j
  cases Nat.decEq i j
  case isTrue h =>
    conv =>
      congr
      intro v
      simp [inc_value_i_vect, h]
      rfl
    apply Nat.Primrec'.comp₁ Nat.succ Nat.Primrec'.succ
    apply decode_primrec'
  case isFalse h =>
    conv =>
      congr
      intro v
      simp [inc_value_i_vect, h]
      rfl
    apply decode_primrec'

theorem clear_value_i_vect_primrec' (m i : Nat) :
    ∀ j : Fin (m + 1), Nat.Primrec' (clear_value_i_vect m i j) := by
  intro j
  cases Nat.decEq i j
  case isTrue h =>
    conv =>
      congr
      intro v
      simp [clear_value_i_vect, h]
      rfl
    apply Nat.Primrec'.const
  case isFalse h =>
    conv =>
      congr
      intro v
      simp [clear_value_i_vect, h]
      rfl
    apply decode_primrec'

def inc_value_i_encode (m i : Nat) : VectNat 1 → Nat :=
  fun z => encode_VectNat m (Vector.ofFn fun j => inc_value_i_vect m i j z)

def clear_value_i_encode (m i : Nat) : VectNat 1 → Nat :=
  fun z => encode_VectNat m (Vector.ofFn fun j => clear_value_i_vect m i j z)

theorem inc_value_i_encode_primrec' (m i : Nat) :
    Nat.Primrec' (inc_value_i_encode m i) :=
  Nat.Primrec'.comp (inc_value_i_vect m i) (encode_VectNat_primrec' m)
    (inc_value_i_vect_primrec' m i)

theorem clear_value_i_encode_primrec' (m i : Nat) :
    Nat.Primrec' (clear_value_i_encode m i) :=
  Nat.Primrec'.comp (clear_value_i_vect m i) (encode_VectNat_primrec' m)
    (clear_value_i_vect_primrec' m i)

def program_execution_fn (p : Program) (n : Nat) : VectNat 1 → Nat := match p with
  | clear_var i => clear_value_i_encode n i
  | increment_var i => inc_value_i_encode n i
  | seq_execution p p' => fun z => program_execution_fn p' n ⟨[program_execution_fn p n z], rfl⟩
  | loop_var i inner =>
    let g_inner := fun z : VectNat 2 =>
      z.head.rec (z.tail.head) fun _ IH => program_execution_fn inner n ⟨[IH], rfl⟩
    fun z => g_inner ⟨[decode_VectNat n i z, z.head], rfl⟩

theorem program_execution_fn_primrec' (p : Program) (n : Nat) :
    Nat.Primrec' (program_execution_fn p n) := by
  induction p
  case clear_var => apply clear_value_i_encode_primrec'
  case increment_var => apply inc_value_i_encode_primrec'
  case loop_var i inner inner_ih =>
    let h : VectNat 3 → Nat := fun z => program_execution_fn inner n ⟨[z.tail.head], rfl⟩
    let g_inner' : VectNat 2 → Nat := fun z =>
      z.head.rec (z.tail.head) fun y IH => h (y ::ᵥ IH ::ᵥ z.tail)
    have h_prec : Nat.Primrec' h :=
        @Nat.Primrec'.comp 3 _ _
        (fun _ z => z.tail.head) inner_ih
        (fun _ => @Nat.Primrec'.tail 2 _ Nat.Primrec'.head)
    have g_inner'_prec : Nat.Primrec' g_inner' :=
      Nat.Primrec'.prec Nat.Primrec'.head h_prec
    let g_inner : VectNat 2 → Nat := fun z =>
      z.head.rec (z.tail.head) fun _ IH => program_execution_fn inner n ⟨[IH], rfl⟩
    have : g_inner = g_inner' := by simp [g_inner', h]
    exact
      @Nat.Primrec'.comp _ _ g_inner
      (fun j => match j with
        | 0 => fun z => decode_VectNat n i z
        | 1 => Vector.head)
      (this.symm.subst g_inner'_prec)
      (fun j => match j with
        | 0 => decode_primrec' n i
        | 1 => Nat.Primrec'.head)

  case seq_execution p p' p_ih p'_ih =>
    have : Nat.Primrec' fun v : VectNat 1 => program_execution_fn p' n ⟨[v.head], rfl⟩ := by
      have : (v : VectNat 1) → ⟨[v.head], rfl⟩ = v := by
        intro v
        let ⟨[x], _⟩ := v
        simp [Vector.head]
      conv =>
        congr
        intro v
        rw [this v]
      exact p'_ih
    exact Nat.Primrec'.comp₁ (fun z => program_execution_fn p' n ⟨[z], rfl⟩)
      this p_ih

theorem decode_program_execution_fn_eq_value_at (p : Program) : ∀ n : Nat, n ≥ highest_var p →
  ∀ v : VectNat (n + 1), ∀ k : Nat,
    value_at (execution_from_state v.toList p) k =
      decode_VectNat n k ⟨[program_execution_fn p n ⟨[encode_VectNat n v], rfl⟩], rfl⟩ := by
  induction p
  case clear_var i =>
    intro n _ _ k
    simp [program_execution_fn, clear_value_i_encode, decode_VectNat_encode]
    simp [execution_from_state, clear_value_clears_value, clear_value_i_vect]
    cases Nat.decLt k (n + 1)
    case isTrue h =>
      simp [h]
      rw [decode_VectNat_encode_value_at]
    case isFalse h =>
      rw [←decode_VectNat_encode_value_at]
      rw [decode_VectNat_encode]
      simp [h]
  case increment_var i =>
    intro n n_h v k
    simp [program_execution_fn, inc_value_i_encode, decode_VectNat_encode]
    simp [execution_from_state, inc_value_increments_value, inc_value_i_vect]
    cases Nat.decLt k (n + 1)
    case isTrue h =>
      simp [h]
      repeat rw [decode_VectNat_encode_value_at]
      cases Nat.decEq i k with | _ h => simp [h]
    case isFalse h =>
      simp [h]
      repeat rw [←decode_VectNat_encode_value_at]
      repeat rw [decode_VectNat_encode]
      simp [h]
      simp [highest_var] at n_h
      have := Nat.lt_of_le_of_lt n_h (Nat.succ_le.mp (Nat.not_lt.mp h))
      have := Nat.lt_iff_le_and_ne.mp this
      exact this.right
  case loop_var i inner inner_ih =>
    intro n n_h v k
    simp [execution_from_state]
    let g_inner : VectNat 2 → Nat := fun z =>
      z.head.rec (z.tail.head) fun _ IH => program_execution_fn inner n ⟨[IH], rfl⟩
    have : program_execution_fn (loop_var i inner) n
        = fun z => g_inner ⟨[(decode_VectNat n i z), z.head], rfl⟩ := by simp [g_inner, program_execution_fn]
    rw [this]
    simp
    rw [decode_VectNat_encode_value_at]
    generalize value_at v.toList i = a
    dsimp [Vector.head]
    revert k
    induction a
    case zero =>
      intros
      simp [loop_n_times, g_inner, Vector.head, Vector.tail]
      rw [decode_VectNat_encode_value_at]
    case succ a a_ih =>
      intro k
      rw [loop_n_times_loop]
      let w : VectNat (n + 1) :=
        Vector.ofFn (fun j => decode_VectNat n j ⟨[g_inner ⟨[a, encode_VectNat n v], rfl⟩], rfl⟩)
      have : ∀ (k : ℕ), value_at (loop_n_times a (Vector.toList v) inner) k = value_at w.toList k := by
        intros
        rw [a_ih, ←decode_VectNat_encode_value_at]
        rw [encode_VectNat_decode]
      rw [same_values_same_execution inner _ w.toList this k]
      have : n ≥ highest_var inner := by
        simp [highest_var] at n_h
        exact n_h.right
      rw [inner_ih n this w k]
      rw [encode_VectNat_decode]
      simp [g_inner, Vector.head, Vector.tail]
  case seq_execution p p' p_ih p'_ih =>
    intro n n_h v k
    dsimp [highest_var] at n_h
    let f_p_h := p_ih n (Nat.le_trans (Nat.le_max_left _ (highest_var p')) n_h)
    let f_p'_h := p'_ih n (Nat.le_trans (Nat.le_max_right (highest_var p) _) n_h)
    simp [program_execution_fn, execution_from_state]
    let w : VectNat (n + 1) :=
      Vector.ofFn (fun j => decode_VectNat n j ⟨[program_execution_fn p n ⟨[encode_VectNat n v], rfl⟩], rfl⟩)
    have : ∀ k : Nat, value_at (execution_from_state v.toList p) k = value_at w.toList k := by
      intros
      rw [f_p_h, ←decode_VectNat_encode_value_at]
      rw [encode_VectNat_decode]
    rw [same_values_same_execution p' _ w.toList this k]
    rw [f_p'_h w k]
    repeat apply congr_arg; apply Vector.eq; simp [Vector.head]
    simp [w]
    rw [encode_VectNat_decode]

def vector_init_state_append_zeros (n k : Nat) : VectNat n → VectNat (n + k + 1) :=
  fun v => 0 ::ᵥ v.append ⟨List.zeros k, List.zeros_length⟩

def program_execution_fn_encode_decode (p : Program) (n k : Nat) :
  VectNat n → Nat := fun v =>
    let z := encode_VectNat (n + k) (vector_init_state_append_zeros n k v)
    let z' := program_execution_fn p (n + k) ⟨[z], rfl⟩
    decode_VectNat (n + k) 0 ⟨[z'], rfl⟩

theorem vector_append_zeros_primrec' (n k : Nat) : Nat.Primrec'.Vec (vector_init_state_append_zeros n k) := by
  intro i
  dsimp [vector_init_state_append_zeros]
  cases Fin.decLe i 0
  case isTrue h =>
    rw [Fin.le_zero_iff.mp h]
    simp
    exact Nat.Primrec'.const 0
  case isFalse h =>
    have : ¬i = 0 := h ∘ Fin.le_zero_iff.mpr
    let ⟨j, j_h⟩ := Fin.eq_succ_of_ne_zero this
    rw [j_h]
    simp
    cases Nat.decLt j n
    case isTrue h =>
      conv =>
        congr
        intro v
        simp [Vector.get_eq_get]
        rw [List.getElem_append j (v.toList_length.symm.subst h)]
      have := @Nat.Primrec'.get n ⟨j, h⟩
      conv at this =>
        congr
        intro v
        simp [Vector.get_eq_get]
      assumption
    case isFalse h =>
      cases k
      case zero =>
        have : j.val < n := j.isLt
        contradiction
      case succ k _ =>
        have h'' : j.val - n < (List.zeros (k + 1)).length := by
          rw [List.zeros_length]
          have := j.isLt
          conv at this =>
            rhs
            rw [Nat.add_comm]
          have := @Nat.sub_lt_sub_right j (k + 1 + n) n (Nat.not_lt.mp h) this
          rw [Nat.add_sub_cancel] at this
          exact this
        have : ∀ v : VectNat n, (v.toList ++ List.zeros (k + 1))[j.val] = 0 := by
          intro v
          have := @List.getElem_append_right Nat j v.toList (List.zeros (k + 1))
            (v.toList_length.substr h) (by simp) (v.toList_length.substr h'')
          rw [this]
          simp
        conv =>
          congr
          intro v
          simp [Vector.get_eq_get]
          rw [this v]
        exact Nat.Primrec'.const 0

theorem program_execution_fn_encode_decode_primrec' (p : Program) (n k : Nat) :
    Nat.Primrec' (program_execution_fn_encode_decode p n k) := by
  let f₁ := encode_VectNat (n + k) ∘ vector_init_state_append_zeros n k
  let f₂ := program_execution_fn p (n + k)
  let f₃ :=  fun v => f₂ ⟨[f₁ v], rfl⟩
  let f₄ : VectNat n → Nat := fun v => decode_VectNat (n + k) 0 ⟨[f₃ v], rfl⟩
  have : program_execution_fn_encode_decode p n k = f₄ := by
    apply funext
    intro v
    simp [program_execution_fn_encode_decode, f₄, f₃, f₂, f₁]
  apply this.symm.subst
  have := Nat.Primrec'.comp'
    (encode_VectNat_primrec' (n + k)) (vector_append_zeros_primrec' n k)
  have f₁_primrec' : Nat.Primrec' f₁ := this
  have f₂_primrec' : Nat.Primrec' f₂ := by dsimp [f₂]; apply program_execution_fn_primrec'
  have f₃_primrec' : Nat.Primrec' f₃ := Nat.Primrec'.comp
    (fun _ => f₁) f₂_primrec' (fun _ => f₁_primrec')
  exact Nat.Primrec'.comp (fun _ => f₃)
    (decode_primrec' (n + k) 0) (fun _ => f₃_primrec')

theorem nary_program_function_primrec' (p : Program) (n : Nat) :
    Nat.Primrec' ⟦ p ⟧^(n) := by
  have : ⟦ p ⟧^(n) = program_execution_fn_encode_decode p n (highest_var p - n) := by
    apply funext
    intro v
    simp [program_execution_fn_encode_decode, vector_init_state_append_zeros]
    have : n + (highest_var p - n) ≥ highest_var p := by
      cases Nat.decLe (highest_var p) n
      case isTrue h =>
        rw [Nat.sub_eq_zero_iff_le.mpr h]
        exact h
      case isFalse h =>
        rw [Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_not_le h)]
    rw [←decode_program_execution_fn_eq_value_at p _ this]
    simp
    rw [←List.cons_append]
    rw [←append_zeros_does_not_change_execution]
    simp [nary_program_function, init_state]
  apply this.symm.subst
  apply program_execution_fn_encode_decode_primrec'

theorem loop_computable_is_primrec' {f : VectNat n → Nat} :
    loop_computable f → Nat.Primrec' f := by
  intro ⟨p, p_h⟩
  have := nary_program_function_primrec' p n
  exact p_h.symm.substr this

theorem loop_computable_iff_primrec' {f : VectNat n → Nat} :
    loop_computable f ↔ Nat.Primrec' f :=
  ⟨loop_computable_is_primrec', primrec'_is_loop_computable⟩

theorem loop_computable_is_computable_cleanly {f : VectNat n → Nat} :
    loop_computable f → loop_computable_cleanly f :=
  primrec'_is_loop_computable_cleanly ∘ loop_computable_is_primrec'

theorem loop_computable_iff_loop_computable_cleanly {f : VectNat n → Nat} :
    loop_computable f ↔ loop_computable_cleanly f :=
  ⟨loop_computable_is_computable_cleanly, loop_computable_cleanly_is_loop_computable⟩

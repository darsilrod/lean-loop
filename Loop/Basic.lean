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
                _ = value_at (execution_from_state (init_state v ++ List.zeros dif) p) 0 := by rw [append_zeros_does_not_change_execution]
                _ = value_at (f v :: v.toList ++ List.zeros dif) 0 := by rw [h v]
                _ = f v := by rfl

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

-- theorem comp_is_loop_computable_cleanly (g : Fin n → VectNat m → Nat) :
--       loop_computable_cleanly f
--     → (∀ i, loop_computable_cleanly (g i))
--     → loop_computable_cleanly fun a => f (Mathlib.Vector.ofFn fun i => g i a) := by
--   sorry

section prec_is_loop_computable_cleanly_proof

variable {n : Nat} {f : VectNat n → Nat} {g : VectNat (n + 2) → Nat} (f_h : cleanly_computes p_f f) (g_h : cleanly_computes p_g g)

-- Part I: construction of the program

def offset (_ : cleanly_computes p_f f) (_ : cleanly_computes p_g g) : Nat :=  max (n + 2) (max (highest_var p_f) (highest_var p_g))

-- Step 1: compute f of the last n inputs
def prec_program_1 : Program :=
  let offset := offset f_h g_h
  let p_1_1 := store_X_1_to_X_succ_n (offset + 1) n
  let p_1_2 := clear_X_j_to_X_n_plus_j 1 n
  let p_1_3 := match (generalizing := false) n with
    | 0 => p_f
    | n + 1 => setup_X_j_to_X_n_plus_j (offset + 1) 1 n ++ p_f
  p_1_1 ++ p_1_2 ++ p_1_3

-- Step 2: compute g counter number of times, for each recursive step
def prec_program_2 : Program :=
  let offset := offset f_h g_h
  let p_2_1 := X 2 += X 0
  let p_2_2 := CLEAR X 0
  let p_2_3 := p_g
  let p_2_4 := CLEAR X 2
  let p_2_5 := INC X 1
  let loop_inner := p_2_1 ++ p_2_2 ++ p_2_3 ++ p_2_4 ++ p_2_5
  let p_loop := LOOP X (offset + 1) DO loop_inner END
  match (generalizing := false) n with
    | 0 => p_loop
    | n + 1 => clear_X_j_to_X_n_plus_j 1 n ++ setup_X_j_to_X_n_plus_j (offset + 1) 3 n ++ p_loop

-- Step 3: Clean up
def prec_program_3 : Program :=
  let offset := offset f_h g_h
  let p_3_1 := match (generalizing := false) n with
    | 0 => CLEAR X 1
    | n + 1 => CLEAR X 1 ++ clear_X_j_to_X_n_plus_j 3 n
  let p_3_2 := match (generalizing := false) n with
    | 0 => X 1 += X (offset + 1)
    | n + 1 => setup_X_j_to_X_n_plus_j (offset + 1) 2 n
  let p_3_3 := clear_Z_0_to_Z_n (offset + 1) n
  p_3_1 ++ p_3_2 ++ p_3_3

def prec_program : Program :=
  let p_1 := prec_program_1 f_h g_h
  let p_2 := prec_program_2 f_h g_h
  let p_3 := prec_program_3 f_h g_h
  p_1 ++ p_2 ++ p_3

-- Part II: calculate the highest variable of the program

theorem prec_program_1_highest_var : highest_var (prec_program_1 f_h g_h) = offset f_h g_h + 1 + n := by
  simp [prec_program_1]
  repeat rewrite [highest_var_concat]
  rewrite [highest_var_store, highest_var_clear]
  simp [highest_var]
  cases n
  case zero =>
    simp_arith
    have : highest_var p_f ≤ offset f_h g_h := by simp [offset]
    exact Nat.le_trans this (Nat.le_add_right _ 1)
  case succ n =>
    rewrite [highest_var_concat, highest_var_setup]
    have : max (n + 1 + 1) (offset f_h g_h + 1 + (n + 1)) = offset f_h g_h + 1 + (n + 1) := by simp_arith
    rewrite [this]
    have : max (n + 1) (offset f_h g_h + 1 + n + 1) = offset f_h g_h + 1 + n + 1 := by simp_arith
    rewrite [this]
    have : max (offset f_h g_h + 1 + n + 1) (highest_var p_f) = offset f_h g_h + 1 + n + 1 := by
      simp_arith
      have : highest_var p_f ≤ offset f_h g_h := by simp [offset]
      exact Nat.le_trans this (Nat.le_add_right _ (n + 2))
    rewrite [this]
    have : (max (offset f_h g_h + 1 + (n + 1)) (offset f_h g_h + 1 + n + 1)) = offset f_h g_h + 1 + n + 1 := by
      repeat rewrite [←Nat.add_assoc]
      exact Nat.max_self _
    rewrite [this]
    simp_arith

theorem prec_program_2_highest_var : highest_var (prec_program_2 f_h g_h) = offset f_h g_h + 1 + n := by

  simp [prec_program_2]
  cases n
  case zero =>
    simp [highest_var]
    constructor
    simp [offset]
    have : highest_var p_g ≤ offset f_h g_h := by simp [offset]
    exact Nat.le_trans this (Nat.le_add_right _ 1)
  case succ n =>
    simp [highest_var, highest_var_clear, highest_var_setup]
    have : max (n + 3) (offset f_h g_h + 1 + n + 1) = offset f_h g_h + 1 + n + 1 := by simp_arith [offset]
    rewrite [this]
    have : max (offset f_h g_h + 1) (max 2 (highest_var p_g)) = offset f_h g_h + 1 := by
      have h1 : offset f_h g_h + 1 ≥ 2 := by simp [offset]
      have h2 : offset f_h g_h + 1 ≥ highest_var p_g := by exact calc
        highest_var p_g ≤ offset f_h g_h := by simp [offset]
                      _ ≤ offset f_h g_h + 1 := by simp_arith
      have := Nat.max_le_of_le_of_le h1 h2
      rewrite [Nat.max_comm]
      exact Nat.max_eq_right this
    rewrite [this]
    have : max (offset f_h g_h + 1 + n + 1) (offset f_h g_h + 1) = offset f_h g_h + 1 + n + 1 := by
      simp
      -- offset f_h g_h ≤ offset f_h g_h + 1 + n
      exact calc
        offset f_h g_h ≤ offset f_h g_h := by exact Nat.le_refl (offset f_h g_h)
                     _ ≤ offset f_h g_h + (1 + n) := by simp
                     _ = offset f_h g_h + 1 + n := by rw [Nat.add_assoc]
    rw [this, Nat.add_assoc]

theorem prec_program_3_highest_var : highest_var (prec_program_3 f_h g_h) = offset f_h g_h + 1 + n := by
  simp [prec_program_3]
  cases n
  case zero =>
    simp [inc_X_i_X_j, highest_var]
  case succ n =>
    simp [highest_var]
    rewrite [highest_var_clear, highest_var_clear_Z, highest_var_setup]
    simp_arith [offset]

theorem prec_program_highest_var : highest_var (prec_program f_h g_h) = offset f_h g_h + 1 + n := by
  simp [prec_program]
  repeat rewrite [highest_var_concat]
  rewrite [prec_program_1_highest_var, prec_program_2_highest_var, prec_program_3_highest_var]
  repeat rw [Nat.max_self]

theorem execution_from_state_prec_program_1_1 (v : VectNat (n + 1)) :
    execution_from_state (0 :: (v.toList ++ 0 :: (List.zeros (offset f_h g_h - (n + 2)) ++  0 :: List.zeros n))) (store_X_1_to_X_succ_n (offset f_h g_h + 1) n)
      = 0 :: v.toList ++ 0 :: List.zeros (offset f_h g_h - (n + 2)) ++ v.toList := by
  let c :=  offset f_h g_h - (n + 2)
  have : offset f_h g_h - (n + 2) = c := rfl
  rewrite [this]
  have : offset f_h g_h + 1 = c + n + 3 := by
    simp [c]
    rewrite [Nat.add_assoc]
    have : n + 2 ≤ offset f_h g_h := Nat.le_max_left _ _
    rw [Nat.sub_add_cancel this]
  rewrite [this]
  let w := 0 :: List.zeros c
  have w_l : w.length = c + 1 := by simp [w, c]
  have := lemma_store (c + 1) n ⟨w, w_l⟩ v
  dsimp [w] at this
  rewrite [zeros_succ] at this
  simp_arith at this
  rewrite [Nat.add_comm c n]
  simp
  exact this

theorem execution_from_state_prec_program_1_2 (v : VectNat (n + 1)) :
    execution_from_state (0 :: v.toList ++ 0 :: List.zeros (offset f_h g_h - (n + 2)) ++ v.toList) (clear_X_j_to_X_n_plus_j 1 n)
      = 0 :: List.zeros (n + 1) ++ 0 :: List.zeros (offset f_h g_h - (n + 2)) ++ v.toList := by
  have : highest_var (clear_X_j_to_X_n_plus_j 1 n) ≤ n + 1 := by
    have : highest_var (clear_X_j_to_X_n_plus_j 1 n) = n + 1 := highest_var_clear
    rewrite [this]
    exact Nat.le_refl _
  have := @execution_from_state_gt_highest_append (clear_X_j_to_X_n_plus_j 1 n) (0 :: List.zeros (offset f_h g_h - (n + 2)) ++ Mathlib.Vector.toList v)
    (n + 1) ⟨0 :: v.toList, by simp⟩ this
  simp at this
  simp
  rw [this, clear_X_lemma]
  simp

theorem execution_from_state_prec_program_1_3 (v : VectNat (n + 1)) :
    execution_from_state (0 :: List.zeros (n + 1) ++ 0 :: List.zeros (offset f_h g_h - (n + 2)) ++ v.toList) (match n with | 0 => p_f | n + 1 => setup_X_j_to_X_n_plus_j (offset f_h g_h + 1) 1 n ++ p_f)
      = f v.tail :: v.tail.toList ++ 0 :: 0 :: List.zeros (offset f_h g_h - (n + 2)) ++ v.toList := by
  cases n
  case zero =>
    simp
    have : 0 :: 0 :: 0 :: (List.zeros (offset f_h g_h - 2) ++ [v.head]) = 0 :: (0 :: 0 :: List.zeros (offset f_h g_h - 2)) ++ [v.head] := by simp
    rewrite [this]
    have z_h : 0 :: 0 :: List.zeros (offset f_h g_h - 2) = List.zeros (offset f_h g_h) := by
      repeat rewrite [←zeros_succ]
      have : offset f_h g_h - 2 + 2 = offset f_h g_h := by
        have : offset f_h g_h ≥ 2 := by simp [offset]
        rw [Nat.sub_add_cancel this]
      rw [this]
    rewrite [z_h]
    have := @cleanly_computable_append_zeros_append_xs 0 p_f f (offset f_h g_h) f_h v.toList Mathlib.Vector.nil (by simp [offset])
    simp [init_state] at this
    simp
    rewrite [this]
    simp
    have : 0 :: 0 :: (List.zeros (offset f_h g_h - 2) ++ [v.head]) = List.zeros (offset f_h g_h) ++ [v.head] := by
      repeat rewrite [←List.cons_append]
      rw [z_h]
    rw [this]
  case succ n =>
    let ⟨x :: xs, xs_l⟩ := v
    simp at xs_l
    rewrite [List.zeros_concat]
    simp [concat_is_seq_execution, execution_from_state, Mathlib.Vector.tail]
    have list_zeros : 0 :: 0 :: List.zeros (offset f_h g_h - (n + 1 + 2)) = List.zeros (offset f_h g_h - (n + 1)) := by
      repeat rewrite [←zeros_succ]
      suffices h : offset f_h g_h - (n + 1 + 2) + 1 + 1 = offset f_h g_h - (n + 1) from by rw [h]
      rewrite [Nat.add_assoc, Nat.sub_add_eq]
      have : 1 + 1 = 2 := rfl
      rewrite [this]
      suffices h : offset f_h g_h - (n + 1) ≥ 2 from Nat.sub_add_cancel h
      suffices h : offset f_h g_h ≥ 2 + (n + 1) from by
        have := Nat.sub_le_sub_right h (n + 1)
        rewrite [Nat.add_sub_cancel 2 (n + 1)] at this
        assumption
      rewrite [Nat.add_comm 2 (n + 1)]
      exact by calc
        offset f_h g_h ≥ n + 1 + 2 := by dsimp [offset]; exact Nat.le_max_left _ _
                     _ = n + 3 := by rw [Nat.add_assoc]
    have : List.zeros (n + 1) ++ 0 :: 0 :: (List.zeros (offset f_h g_h - (n + 1 + 2)) ++ x :: xs)
      = List.zeros (n + 1) ++ List.zeros (offset f_h g_h - (n + 1)) ++ x :: xs := by exact calc
            List.zeros (n + 1) ++ 0 :: 0 :: (List.zeros (offset f_h g_h - (n + 1 + 2)) ++x :: xs)
                = List.zeros (n + 1) ++ (0 :: 0 :: List.zeros (offset f_h g_h - (n + 1 + 2))) ++ x :: xs := by simp
              _ = List.zeros (n + 1) ++ List.zeros (offset f_h g_h - (n + 1)) ++ x :: xs := by rw [list_zeros]
    rewrite [this]
    have : (xs ++ 0 :: 0 :: (List.zeros (offset f_h g_h - (n + 1 + 2)) ++ x :: xs))
      = xs ++ List.zeros (offset f_h g_h - (n + 1)) ++ x :: xs := by exact calc
            xs ++ 0 :: 0 :: (List.zeros (offset f_h g_h - (n + 1 + 2)) ++ x :: xs)
                = xs ++ (0 :: 0 :: List.zeros (offset f_h g_h - (n + 1 + 2))) ++ x :: xs := by simp
              _ = xs ++ List.zeros (offset f_h g_h - (n + 1)) ++ x :: xs := by rw [list_zeros]
    rewrite [this]
    --
    have : List.zeros (n + 1) ++ List.zeros (offset f_h g_h - (n + 1)) ++ x :: xs
      = List.zeros (n + 1) ++ (List.zeros (offset f_h g_h - (n + 1)) ++ [x]) ++ xs := by rewrite [List.append_assoc] ; simp
    rewrite [this]
    have : (List.zeros (offset f_h g_h - (n + 1)) ++ [x]).length = offset f_h g_h - n := by
      simp
      rewrite [Nat.sub_add_eq]
      suffices h : offset f_h g_h - n ≥ 1 from Nat.sub_add_cancel h
      exact calc
        offset f_h g_h - n ≥ (n + 1 + 2) - n := by
          dsimp [offset]
          exact Nat.sub_le_sub_right (Nat.le_max_left (n + 1 + 2) (max (highest_var p_f) (highest_var p_g))) n
        _ ≥ 1 := by
          rewrite [Nat.add_comm, Nat.add_comm n, ←Nat.add_assoc, Nat.add_sub_cancel]
          simp_arith
    have := lemma_setup (offset f_h g_h - n) n ⟨List.zeros (offset f_h g_h - (n + 1)) ++ [x], this⟩ ⟨xs, xs_l⟩
    dsimp [Mathlib.Vector.toList] at this

    have lemm_eq : n + (offset f_h g_h - n) + 1 = offset f_h g_h + 1 := by
      simp_arith
      rewrite [Nat.add_comm]
      suffices h : n ≤ offset f_h g_h from by exact Nat.sub_add_cancel h
      exact by calc
        n ≤ n + 1 + 2 := by simp_arith
        _  ≤ offset f_h g_h := by dsimp [offset]; exact Nat.le_max_left _ _
    rewrite [lemm_eq] at this
    rewrite [this]
    rewrite [←List.cons_append, ←List.cons_append]
    rewrite [←List.append_assoc]
    have : offset f_h g_h - (n + 1) ≥ highest_var p_f - (n + 1) := by
      suffices h : offset f_h g_h ≥ highest_var p_f from Nat.sub_le_sub_right h (n + 1)
      simp [offset]
    have := cleanly_computable_append_zeros_append_xs f_h ([x] ++ xs) ⟨xs, xs_l⟩ this
    simp [init_state] at this
    simp
    rw [this]

theorem execution_from_state_prec_program_1 (v : VectNat (n + 1)) :
    execution_from_state (0 :: v.toList ++ 0 :: List.zeros (offset f_h g_h - (n + 2)) ++ 0 :: List.zeros n) (prec_program_1 f_h g_h)
      = f v.tail :: v.tail.toList ++ 0 :: 0 :: List.zeros (offset f_h g_h - (n + 2)) ++ v.toList := by
  let p_1_1 := store_X_1_to_X_succ_n (offset f_h g_h + 1) n
  let p_1_2 := clear_X_j_to_X_n_plus_j 1 n
  let p_1_3 := match n with
    | 0 => p_f
    | n + 1 => setup_X_j_to_X_n_plus_j (offset f_h g_h + 1) 1 n ++ p_f
  have : prec_program_1 f_h g_h = p_1_1 ++ p_1_2 ++ p_1_3:= by
    dsimp [prec_program_1, p_1_1, p_1_2, p_1_3]

  rewrite [this]
  repeat rewrite [concat_is_seq_execution]
  simp [execution_from_state]
  dsimp [p_1_1, p_1_2, p_1_3]
  rewrite [execution_from_state_prec_program_1_1, execution_from_state_prec_program_1_2,
    execution_from_state_prec_program_1_3]
  simp

-- 0 :: 0 :: 0 :: List.zeros n ++ List.zeros (offset f_h g_h - (n + 2)) ++ 0 :: (f v.tail) :: v.toList
-- 0 :: k :: 0 :: List.zeros n ++ List.zeros (offset f_h g_h - (n + 2)) ++ 0 :: (f v.tail) :: v.toList
-- theorem execution_from_state_prec_program_2_1 : 2 = 3 := by
--   sorry

-- TODO: check if clear is correct
-- theorem execution_from_state_prec_program_2_1 (f_h : cleanly_computes p_f f) (g_h : cleanly_computes p_g g) (v : VectNat (n + 1)) :
--     execution_from_state (0 :: v.tail.toList ++ 0 :: 0 :: List.zeros (offset f_h g_h - (n + 2)) ++ (f v.tail) :: v.toList) (clear_X_j_to_X_n_plus_j 1 n)
--       = 0 :: 0 :: 0 :: List.zeros n ++ List.zeros (offset f_h g_h - (n + 2)) ++ 0 :: (f v.tail) :: v.toList := by
--   have : 0 :: List.zeros (offset f_h g_h - (n + 2)) = List.zeros (offset f_h g_h - (n + 2)) ++ [0] := by rw [←zeros_succ, List.zeros_concat]
--   have := by exact calc
--       0 :: v.tail.toList ++ 0 :: 0 :: List.zeros (offset f_h g_h - (n + 2)) ++ (f v.tail) :: v.toList
--         = 0 :: v.tail.toList ++ 0 :: (0 :: List.zeros (offset f_h g_h - (n + 2))) ++ (f v.tail) :: v.toList := by simp
--       _ = 0 :: v.tail.toList ++ 0 :: (List.zeros (offset f_h g_h - (n + 2)) ++ [0]) ++ f v.tail :: v.toList := by rw [this]
--       _ = 0 :: v.tail.toList ++ 0 :: List.zeros (offset f_h g_h - (n + 2)) ++ 0 :: (f v.tail) :: v.toList := by simp
--   rewrite [this]
--   -- have : highest_var (clear_X_j_to_X_n_plus_j 1 n) ≤ n + 1 := by
--   --   have : highest_var (clear_X_j_to_X_n_plus_j 1 n) = n + 1 := highest_var_clear
--   --   rewrite [this]
--   --   exact Nat.le_refl _

--   -- have := @execution_from_state_gt_highest_append (clear_X_j_to_X_n_plus_j 1 n)
--   --   (0 :: List.zeros (offset f_h g_h - (n + 2)) ++ 0 :: (f v.tail) :: v.toList) n (0 ::ᵥ v.tail) this
--   -- simp at this
--   sorry


end prec_is_loop_computable_cleanly_proof

/-
theorem prec_is_loop_computable_cleanly {f : VectNat n → Nat}
    {g : VectNat (n + 2) → Nat} : loop_computable_cleanly f
    → loop_computable_cleanly g
    → loop_computable_cleanly fun v : VectNat (n + 1) =>
      v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail) := by
  intro ⟨p_f, f_h⟩ ⟨p_g, g_h⟩

  -- Part II: rewriting to analyise the program more easily
  have : highest_var p = offset + n + 2 := by
    simp [p, concat_is_seq_execution]
    repeat rw [highest_var]
    rw [highest_var_p_1, highest_var_p_2, highest_var_p_3]
    simp_arith [Z]
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
  let h : VectNat (n + 1) → Nat := fun v => Nat.rec (f v.tail) (fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) v.head
  have : (fun v =>
    Nat.rec (f (Mathlib.Vector.tail v)) (fun y IH => g (y ::ᵥ IH ::ᵥ Mathlib.Vector.tail v))
    (Mathlib.Vector.head v)) v = h v := rfl
  rw [this]
  -- let ⟨x :: xs, v_length⟩ := v
  -- simp
  -- let w : VectNat n := ⟨xs, by simp at v_length; exact v_length⟩
  -- have : ⟨x :: xs, v_length⟩ = x ::ᵥ w := rfl
  -- rw [this]
  -- Part three: analyse each part of the program


  have execution_p_1_1 : execution_from_state (0 :: v.toList ++ 0 :: List.zeros padding ++ 0 :: 0 :: List.zeros n) p_1_1
      = 0 :: v.toList ++ 0 :: List.zeros padding ++ 0 :: v.toList := by
    sorry

  have execution_p_1_2 : execution_from_state (0 :: v.toList ++ 0 :: List.zeros padding ++ 0 :: v.toList) p_1_2
      = 0 :: List.zeros (n + 1) ++ 0 :: List.zeros padding ++ 0 :: v.toList := by
    sorry

  have execution_p_1_3 : execution_from_state (0 :: List.zeros (n + 1) ++ 0 :: List.zeros padding ++ 0 :: v.toList) p_1_3
      = (f v.tail) :: v.tail.toList ++ 0 :: 0 :: List.zeros padding ++ 0 :: v.toList := by
    sorry

  have execution_p_1_4 : execution_from_state ((f v.tail) :: v.tail.toList ++ 0 :: 0 :: List.zeros padding ++ 0 :: v.toList) p_1_4
      = (f v.tail) :: v.tail.toList ++ 0 :: 0 :: List.zeros padding ++ (f v.tail) :: v.toList := by
    sorry

  have execution_p_1_5 : execution_from_state ((f v.tail) :: v.tail.toList ++ 0 :: 0 :: List.zeros padding ++ (f v.tail) :: v.toList) p_1_5
      = 0 :: v.tail.toList ++ 0 :: 0 :: List.zeros padding ++ (f v.tail) :: v.toList := by
    simp [p_1_5, execution_from_state]
    rw [clear_value_cons_zero]

  have execution_p_1 : execution_from_state (0 :: v.toList ++ 0 :: List.zeros padding ++ 0 :: 0 :: List.zeros n) p_1
      = 0 :: v.tail.toList ++ 0 :: 0 :: List.zeros padding ++ (f v.tail) :: v.toList := by
    exact calc
      execution_from_state (0 :: v.toList ++ 0 :: List.zeros padding ++ 0 :: 0 :: List.zeros n) p_1
        =
      execution_from_state (0 :: v.toList ++ 0 :: List.zeros padding ++ 0 :: 0 :: List.zeros n) (p_1_1 ++ p_1_2 ++ p_1_3 ++ p_1_4 ++ p_1_5) := rfl
      _ =
      execution_from_state (0 :: v.toList ++ 0 :: List.zeros padding ++ 0 :: v.toList) (p_1_2 ++ p_1_3 ++ p_1_4 ++ p_1_5)  := by sorry
      _ =
      execution_from_state (0 :: List.zeros (n + 1) ++ 0 :: List.zeros padding ++ 0 :: v.toList) (p_1_3 ++ p_1_4 ++ p_1_5) := by sorry
      _ =
      execution_from_state ((f v.tail) :: v.tail.toList ++ 0 :: 0 :: List.zeros padding ++ 0 :: v.toList) (p_1_4 ++ p_1_5) := by sorry
      _ =
      execution_from_state ((f v.tail) :: v.tail.toList ++ 0 :: 0 :: List.zeros padding ++ (f v.tail) :: v.toList) p_1_5 := by sorry
      _ =
      0 :: v.tail.toList ++ 0 :: 0 :: List.zeros padding ++ (f v.tail) :: v.toList := execution_p_1_5

  --




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
-/

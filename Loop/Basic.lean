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
    loop_inc_adds_value, value_at_cons_succ, value_at, Vector.get_eq_get]

section prec_is_loop_computable_cleanly_proof

variable
  {n : Nat}
  {f : VectNat n → Nat}
  {g : VectNat (n + 2) → Nat}
  (f_h : cleanly_computes p_f f)
  (g_h : cleanly_computes p_g g)

-- Part I: construction of the program

def offset_pr (_ : cleanly_computes p_f f) (_ : cleanly_computes p_g g) : Nat :=  max (n + 2) (max (highest_var p_f) (highest_var p_g))

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

theorem prec_program_1_highest_var : highest_var (prec_program_1 f_h g_h) = offset_pr f_h g_h + 1 + n := by
  simp [prec_program_1]
  repeat rewrite [highest_var_concat]
  rewrite [highest_var_store, highest_var_clear]
  simp [highest_var]
  cases n
  case zero =>
    simp_arith
    have : highest_var p_f ≤ offset_pr f_h g_h := by simp [offset_pr ]
    exact Nat.le_trans this (Nat.le_add_right _ 1)
  case succ n =>
    rewrite [highest_var_concat, highest_var_setup]
    have : max (n + 1 + 1) (offset_pr f_h g_h + 1 + (n + 1)) = offset_pr f_h g_h + 1 + (n + 1) := by simp_arith
    rewrite [this]
    have : max (n + 1) (offset_pr f_h g_h + 1 + n + 1) = offset_pr f_h g_h + 1 + n + 1 := by simp_arith
    rewrite [this]
    have : max (offset_pr f_h g_h + 1 + n + 1) (highest_var p_f) = offset_pr f_h g_h + 1 + n + 1 := by
      simp_arith
      have : highest_var p_f ≤ offset_pr f_h g_h := by simp [offset_pr ]
      exact Nat.le_trans this (Nat.le_add_right _ (n + 2))
    rewrite [this]
    have : (max (offset_pr f_h g_h + 1 + (n + 1)) (offset_pr f_h g_h + 1 + n + 1)) = offset_pr f_h g_h + 1 + n + 1 := by
      repeat rewrite [←Nat.add_assoc]
      exact Nat.max_self _
    rewrite [this]
    simp_arith

theorem prec_program_2_highest_var : highest_var (prec_program_2 f_h g_h) = offset_pr f_h g_h + 1 + n := by

  simp [prec_program_2]
  cases n
  case zero =>
    simp [highest_var]
    constructor
    simp [offset_pr ]
    have : highest_var p_g ≤ offset_pr f_h g_h := by simp [offset_pr ]
    exact Nat.le_trans this (Nat.le_add_right _ 1)
  case succ n =>
    simp [highest_var, highest_var_clear, highest_var_setup]
    have : max (n + 3) (offset_pr f_h g_h + 1 + n + 1) = offset_pr f_h g_h + 1 + n + 1 := by simp_arith [offset_pr ]
    rewrite [this]
    have : max (offset_pr f_h g_h + 1) (max 2 (highest_var p_g)) = offset_pr f_h g_h + 1 := by
      have h1 : offset_pr f_h g_h + 1 ≥ 2 := by simp [offset_pr ]
      have h2 : offset_pr f_h g_h + 1 ≥ highest_var p_g := by exact calc
        highest_var p_g ≤ offset_pr f_h g_h := by simp [offset_pr ]
                      _ ≤ offset_pr f_h g_h + 1 := by simp_arith
      have := Nat.max_le_of_le_of_le h1 h2
      rewrite [Nat.max_comm]
      exact Nat.max_eq_right this
    rewrite [this]
    have : max (offset_pr f_h g_h + 1 + n + 1) (offset_pr f_h g_h + 1) = offset_pr f_h g_h + 1 + n + 1 := by
      simp
      -- offset_pr f_h g_h ≤ offset_pr f_h g_h + 1 + n
      exact calc
        offset_pr f_h g_h ≤ offset_pr f_h g_h := by exact Nat.le_refl (offset_pr f_h g_h)
                     _ ≤ offset_pr f_h g_h + (1 + n) := by simp
                     _ = offset_pr f_h g_h + 1 + n := by rw [Nat.add_assoc]
    rw [this, Nat.add_assoc]

theorem prec_program_3_highest_var : highest_var (prec_program_3 f_h g_h) = offset_pr f_h g_h + 1 + n := by
  simp [prec_program_3]
  cases n
  case zero =>
    simp [highest_var]
  case succ n =>
    simp [highest_var]
    rewrite [highest_var_clear, highest_var_clear_Z, highest_var_setup]
    simp_arith [offset_pr ]

theorem prec_program_highest_var : highest_var (prec_program f_h g_h) = offset_pr f_h g_h + 1 + n := by
  simp [prec_program]
  repeat rewrite [highest_var_concat]
  rewrite [prec_program_1_highest_var, prec_program_2_highest_var, prec_program_3_highest_var]
  repeat rw [Nat.max_self]

theorem execution_from_state_prec_program_1_1 (v : VectNat (n + 1)) :
    execution_from_state (0 :: (v.toList ++ 0 :: (List.zeros (offset_pr f_h g_h - (n + 2)) ++  0 :: List.zeros n))) (store_X_1_to_X_succ_n (offset_pr f_h g_h + 1) n)
      = 0 :: v.toList ++ 0 :: List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  let c :=  offset_pr f_h g_h - (n + 2)
  have : offset_pr f_h g_h - (n + 2) = c := rfl
  rewrite [this]
  have : offset_pr f_h g_h + 1 = c + n + 3 := by
    simp [c]
    rewrite [Nat.add_assoc]
    have : n + 2 ≤ offset_pr f_h g_h := Nat.le_max_left _ _
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
    execution_from_state (0 :: v.toList ++ 0 :: List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList) (clear_X_j_to_X_n_plus_j 1 n)
      = 0 :: List.zeros (n + 1) ++ 0 :: List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  have : highest_var (clear_X_j_to_X_n_plus_j 1 n) ≤ n + 1 := by
    have : highest_var (clear_X_j_to_X_n_plus_j 1 n) = n + 1 := highest_var_clear
    rewrite [this]
    exact Nat.le_refl _
  have := @execution_from_state_gt_highest_append (clear_X_j_to_X_n_plus_j 1 n) (0 :: List.zeros (offset_pr f_h g_h - (n + 2)) ++ Vector.toList v)
    (n + 1) ⟨0 :: v.toList, by simp⟩ this
  simp at this
  simp
  rw [this, clear_X_1_lemma]
  simp

theorem execution_from_state_prec_program_1_3 (v : VectNat (n + 1)) :
    execution_from_state (0 :: List.zeros (n + 1) ++ 0 :: List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList) (match n with | 0 => p_f | n + 1 => setup_X_j_to_X_n_plus_j (offset_pr f_h g_h + 1) 1 n ++ p_f)
      = f v.tail :: v.tail.toList ++ 0 :: 0 :: List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  cases n
  case zero =>
    simp
    have : 0 :: 0 :: 0 :: (List.zeros (offset_pr f_h g_h - 2) ++ [v.head]) = 0 :: (0 :: 0 :: List.zeros (offset_pr f_h g_h - 2)) ++ [v.head] := by simp
    rewrite [this]
    have z_h : 0 :: 0 :: List.zeros (offset_pr f_h g_h - 2) = List.zeros (offset_pr f_h g_h) := by
      repeat rewrite [←zeros_succ]
      have : offset_pr f_h g_h - 2 + 2 = offset_pr f_h g_h := by
        have : offset_pr f_h g_h ≥ 2 := by simp [offset_pr ]
        rw [Nat.sub_add_cancel this]
      rw [this]
    rewrite [z_h]
    have := @cleanly_computable_append_zeros_append_xs 0 p_f f (offset_pr f_h g_h) f_h v.toList Vector.nil (by simp [offset_pr ])
    simp [init_state] at this
    simp
    rewrite [this]
    simp
    have : 0 :: 0 :: (List.zeros (offset_pr f_h g_h - 2) ++ [v.head]) = List.zeros (offset_pr f_h g_h) ++ [v.head] := by
      repeat rewrite [←List.cons_append]
      rw [z_h]
    rw [this]
  case succ n =>
    let ⟨x :: xs, xs_l⟩ := v
    simp at xs_l
    rewrite [List.zeros_concat]
    simp [concat_is_seq_execution, execution_from_state, Vector.tail]
    have list_zeros : 0 :: 0 :: List.zeros (offset_pr f_h g_h - (n + 1 + 2)) = List.zeros (offset_pr f_h g_h - (n + 1)) := by
      repeat rewrite [←zeros_succ]
      suffices h : offset_pr f_h g_h - (n + 1 + 2) + 1 + 1 = offset_pr f_h g_h - (n + 1) from by rw [h]
      rewrite [Nat.add_assoc, Nat.sub_add_eq]
      have : 1 + 1 = 2 := rfl
      rewrite [this]
      suffices h : offset_pr f_h g_h - (n + 1) ≥ 2 from Nat.sub_add_cancel h
      suffices h : offset_pr f_h g_h ≥ 2 + (n + 1) from by
        have := Nat.sub_le_sub_right h (n + 1)
        rewrite [Nat.add_sub_cancel 2 (n + 1)] at this
        assumption
      rewrite [Nat.add_comm 2 (n + 1)]
      exact by calc
        offset_pr f_h g_h ≥ n + 1 + 2 := by dsimp [offset_pr ]; exact Nat.le_max_left _ _
                     _ = n + 3 := by rw [Nat.add_assoc]
    have : List.zeros (n + 1) ++ 0 :: 0 :: (List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ x :: xs)
      = List.zeros (n + 1) ++ List.zeros (offset_pr f_h g_h - (n + 1)) ++ x :: xs := by exact calc
            List.zeros (n + 1) ++ 0 :: 0 :: (List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++x :: xs)
                = List.zeros (n + 1) ++ (0 :: 0 :: List.zeros (offset_pr f_h g_h - (n + 1 + 2))) ++ x :: xs := by simp
              _ = List.zeros (n + 1) ++ List.zeros (offset_pr f_h g_h - (n + 1)) ++ x :: xs := by rw [list_zeros]
    rewrite [this]
    have : (xs ++ 0 :: 0 :: (List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ x :: xs))
      = xs ++ List.zeros (offset_pr f_h g_h - (n + 1)) ++ x :: xs := by exact calc
            xs ++ 0 :: 0 :: (List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ x :: xs)
                = xs ++ (0 :: 0 :: List.zeros (offset_pr f_h g_h - (n + 1 + 2))) ++ x :: xs := by simp
              _ = xs ++ List.zeros (offset_pr f_h g_h - (n + 1)) ++ x :: xs := by rw [list_zeros]
    rewrite [this]
    --
    have : List.zeros (n + 1) ++ List.zeros (offset_pr f_h g_h - (n + 1)) ++ x :: xs
      = List.zeros (n + 1) ++ (List.zeros (offset_pr f_h g_h - (n + 1)) ++ [x]) ++ xs := by rewrite [List.append_assoc] ; simp
    rewrite [this]
    have : (List.zeros (offset_pr f_h g_h - (n + 1)) ++ [x]).length = offset_pr f_h g_h - n := by
      simp
      rewrite [Nat.sub_add_eq]
      suffices h : offset_pr f_h g_h - n ≥ 1 from Nat.sub_add_cancel h
      exact calc
        offset_pr f_h g_h - n ≥ (n + 1 + 2) - n := by
          dsimp [offset_pr ]
          exact Nat.sub_le_sub_right (Nat.le_max_left (n + 1 + 2) (max (highest_var p_f) (highest_var p_g))) n
        _ ≥ 1 := by
          rewrite [Nat.add_comm, Nat.add_comm n, ←Nat.add_assoc, Nat.add_sub_cancel]
          simp_arith
    have := lemma_setup_X_1 (offset_pr f_h g_h - n) n ⟨List.zeros (offset_pr f_h g_h - (n + 1)) ++ [x], this⟩ ⟨xs, xs_l⟩
    dsimp [Vector.toList] at this

    have lemm_eq : n + (offset_pr f_h g_h - n) + 1 = offset_pr f_h g_h + 1 := by
      simp_arith
      rewrite [Nat.add_comm]
      suffices h : n ≤ offset_pr f_h g_h from by exact Nat.sub_add_cancel h
      exact by calc
        n ≤ n + 1 + 2 := by simp_arith
        _  ≤ offset_pr f_h g_h := by dsimp [offset_pr ]; exact Nat.le_max_left _ _
    rewrite [lemm_eq] at this
    rewrite [this]
    rewrite [←List.cons_append, ←List.cons_append]
    rewrite [←List.append_assoc]
    have : offset_pr f_h g_h - (n + 1) ≥ highest_var p_f - (n + 1) := by
      suffices h : offset_pr f_h g_h ≥ highest_var p_f from Nat.sub_le_sub_right h (n + 1)
      simp [offset_pr ]
    have := cleanly_computable_append_zeros_append_xs f_h ([x] ++ xs) ⟨xs, xs_l⟩ this
    simp [init_state] at this
    simp
    rw [this]

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

  rewrite [this]
  repeat rewrite [concat_is_seq_execution]
  simp [execution_from_state]
  dsimp [p_1_1, p_1_2, p_1_3]
  rewrite [execution_from_state_prec_program_1_1, execution_from_state_prec_program_1_2,
    execution_from_state_prec_program_1_3]
  simp

theorem execution_from_state_prec_program_2_1 (R k : Nat) (v : VectNat (n + 1)) :
    execution_from_state (R :: k :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList) (X 2 += X 0)
      = R :: k :: R :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  exact calc
      execution_from_state (R :: k :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList) (X 2 += X 0)
    = execution_from_state ([R, k] ++ 0 :: (v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList)) (X 2 += X 0) := by simp
  _ = R :: k :: R :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
      have : [R, k].length = 2 := rfl
      rewrite [inc_X_i_X_j_adds_value this]
      simp [value_at]

theorem execution_from_state_prec_program_2_2 (R k : Nat) (v : VectNat (n + 1)) :
    execution_from_state (R :: k :: R :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList) (CLEAR X 0)
      = 0 :: k :: R :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  simp [execution_from_state, clear_value]

theorem execution_from_state_prec_program_2_3 (R k : Nat) (v : VectNat (n + 1)) :
    execution_from_state (0 :: k :: R :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList) p_g
      = g (k ::ᵥ R ::ᵥ v.tail) :: k :: R :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  have : offset_pr f_h g_h - (n + 2) ≥ highest_var p_g - (n + 2) := by
    have : offset_pr f_h g_h ≥ highest_var p_g := by simp [offset_pr ]
    exact Nat.sub_le_sub_right this (n + 2)
  have := cleanly_computable_append_zeros_append_xs g_h v.toList (k ::ᵥ R ::ᵥ v.tail) this
  simp [init_state] at this
  simp
  exact this

theorem execution_from_state_prec_program_2_4 (R k : Nat) (v : VectNat (n + 1)) :
    execution_from_state (g (k ::ᵥ R ::ᵥ v.tail) :: k :: R :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList) (CLEAR X 2)
      = g (k ::ᵥ R ::ᵥ v.tail) :: k :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  simp [execution_from_state, clear_value]

theorem execution_from_state_prec_program_2_5 (R k : Nat) (v : VectNat (n + 1)) :
    execution_from_state (g (k ::ᵥ R ::ᵥ v.tail) :: k :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList) (INC X 1)
      = g (k ::ᵥ R ::ᵥ v.tail) :: (k + 1) :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  simp [execution_from_state, inc_value]

theorem execution_from_state_prec_program_loop_inner (R k : Nat) (v : VectNat (n + 1)) :
  execution_from_state (R :: k :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList) (X 2 += X 0 ++ CLEAR X 0 ++ p_g ++ CLEAR X 2 ++ INC X 1)
      = g (k ::ᵥ R ::ᵥ v.tail) :: (k + 1) :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  repeat rewrite [concat_is_seq_execution]
  repeat rewrite [seq_execution_unfold]
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
  simp [execution_from_state]
  have : value_at (f ⟨xs, xs_l⟩ :: 0 :: 0 :: (xs ++ (List.zeros (offset_pr f_h g_h - (n + 2)) ++ x :: xs))) (offset_pr f_h g_h + 1)
      = x := by
    exact calc
          value_at (f ⟨xs, xs_l⟩ :: 0 :: 0 :: (xs ++ (List.zeros (offset_pr f_h g_h - (n + 2)) ++ x :: xs))) (offset_pr f_h g_h + 1)
        = value_at ((f ⟨xs, xs_l⟩ :: 0 :: 0 :: xs ++ List.zeros (offset_pr f_h g_h - (n + 2))) ++ x :: xs) (offset_pr f_h g_h + 1) := by simp
      _ = x := by
          have : (f ⟨xs, xs_l⟩ :: 0 :: 0 :: xs ++ List.zeros (offset_pr f_h g_h - (n + 2))).length = offset_pr f_h g_h + 1 := by
            simp [xs_l]
            rewrite [Nat.add_assoc, Nat.add_comm _ 2, ←Nat.add_assoc, Nat.add_comm, Nat.add_comm 2 n]
            suffices h : offset_pr f_h g_h ≥ n + 2 from Nat.sub_add_cancel h
            simp [offset_pr ]
          exact value_at_n this

  rewrite [this]
  suffices h : ∀ k : Nat, loop_n_times k (f ⟨xs, xs_l⟩ :: 0 :: 0 :: (xs ++ (List.zeros (offset_pr f_h g_h - (n + 2)) ++ x :: xs)))
      (X 2 += X 0 ++ CLEAR X 0 ++ p_g ++ CLEAR X 2 ++ INC X 1)
      = Nat.rec (f ⟨xs, xs_l⟩) (fun y IH ↦ g (y ::ᵥ IH ::ᵥ ⟨xs, xs_l⟩)) k :: k :: 0 :: (xs ++ (List.zeros (offset_pr f_h g_h - (n + 2)) ++ x :: xs)) from h x
  intro k
  induction k
  case zero =>
    simp [loop_n_times]
  case succ k k_ih =>
    rewrite [loop_n_times_loop, k_ih]
    have := execution_from_state_prec_program_loop_inner f_h g_h
      (Nat.rec (f ⟨xs, xs_l⟩) (fun y IH ↦ g (y ::ᵥ IH ::ᵥ ⟨xs, xs_l⟩)) k)
      k ⟨x :: xs, by simp [xs_l]⟩
    simp [Vector.tail, Vector.toList] at this
    simp
    rw [this]

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
    repeat rewrite [concat_is_seq_execution]
    repeat rewrite [seq_execution_unfold]
    suffices h : execution_from_state
      (execution_from_state
        (f (Vector.tail v) ::
          ((Vector.tail v).toList ++ 0 :: 0 :: List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++
            Vector.toList v))
        (clear_X_j_to_X_n_plus_j 1 n))
          (setup_X_j_to_X_n_plus_j (offset_pr f_h g_h + 1) 3 n)
        = f v.tail :: 0 :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ v.toList from by
      rewrite [h]
      have := execution_from_state_prec_program_loop f_h g_h v
      simp [concat_is_seq_execution] at this
      simp
      rw [this]
    let ⟨x :: xs, xs_l⟩ := v
    simp_arith at xs_l
    dsimp [Vector.tail]

    have := calc
        execution_from_state (f ⟨xs, xs_l⟩ :: (xs ++ 0 :: 0 :: List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ x :: xs))
          (clear_X_j_to_X_n_plus_j 1 n)
        = execution_from_state ((f ⟨xs, xs_l⟩ :: xs) ++ (0 :: 0 :: List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ x :: xs))
         (clear_X_j_to_X_n_plus_j 1 n) := by simp
      _ = (execution_from_state (f ⟨xs, xs_l⟩ :: xs) (clear_X_j_to_X_n_plus_j 1 n))
        ++ 0 :: 0 :: List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ x :: xs := by
          have h := @execution_from_state_gt_highest_append (clear_X_j_to_X_n_plus_j 1 n)
            (0 :: 0 :: List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ x :: xs)
            (n + 1) (f ⟨xs, xs_l⟩ ::ᵥ ⟨xs, xs_l⟩) (by rw [highest_var_clear])
          have : (f ⟨xs, xs_l⟩ ::ᵥ ⟨xs, xs_l⟩).toList = f ⟨xs, xs_l⟩ :: xs := by simp
          rewrite [this] at h
          rw [h]
          simp
      _ = f ⟨xs, xs_l⟩ :: List.zeros (n + 1) ++ 0 :: 0 :: List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ x :: xs := by
          suffices h : execution_from_state (f ⟨xs, xs_l⟩ :: xs) (clear_X_j_to_X_n_plus_j 1 n) = f ⟨xs, xs_l⟩ :: List.zeros (n + 1) from by rw [h]
          rw [clear_X_succ]
          let v' : VectNat (n + 1) := ⟨xs, xs_l⟩
          have : execution_from_state xs (clear_X_j_to_X_n_plus_j 0 n)
            = execution_from_state (v'.toList) (clear_X_j_to_X_n_plus_j 0 n) := by simp [v']
          rw [this, clear_X_lemma]
      _ = f ⟨xs, xs_l⟩ ::(List.zeros (n + 1) ++ [0] ++ [0]) ++ List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ x :: xs := by simp
      _ = f ⟨xs, xs_l⟩ :: List.zeros (n + 3) ++ List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ x :: xs := by rw [←List.zeros_concat, ←List.zeros_concat]
      _ = f ⟨xs, xs_l⟩ ::  0 :: 0 :: List.zeros (n + 1) ++ List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ x :: xs := by rw [zeros_succ, zeros_succ]
      _ = f ⟨xs, xs_l⟩ ::  (0 :: (0 :: (List.zeros (n + 1) ++ List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ [x] ++ xs))) := by simp
      _ = f ⟨xs, xs_l⟩ ::  (0 :: (0 :: (List.zeros (n + 1) ++ (List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ [x]) ++ xs))) := by repeat rw [List.append_assoc]

    rewrite [this]
    have : offset_pr f_h g_h + 1 = (offset_pr f_h g_h - 2) + 3 := by
      suffices h : offset_pr f_h g_h ≥ 2 from by exact calc
        offset_pr f_h g_h + 1 = (offset_pr f_h g_h - 2 + 2) + 1 := by rw [Nat.sub_add_cancel h]
                         _ = (offset_pr f_h g_h - 2) + 3 := by simp_arith
      simp_arith [offset_pr ]
    rewrite [this]
    repeat rewrite [setup_X_succ]
    have := lemma_setup (offset_pr f_h g_h - (n + 1 + 2) + 1) n ⟨List.zeros (offset_pr f_h g_h - (n + 1 + 2)) ++ [x], by simp⟩ ⟨xs, xs_l⟩
    dsimp at this
    have h_eq : n + (offset_pr f_h g_h - (n + 1 + 2) + 1) = offset_pr f_h g_h - 2 := by
      rewrite [Nat.add_comm (n + 1), Nat.add_comm, Nat.add_assoc, Nat.add_comm 1 n, Nat.sub_add_eq]
      suffices h : offset_pr f_h g_h - 2 ≥ n + 1 from Nat.sub_add_cancel h
      have : offset_pr f_h g_h ≥ n + 2 + 1 := by simp [offset_pr ]
      have := Nat.sub_le_sub_right this 2
      have h : n + 2 + 1 - 2 = n + 1 := by simp
      rewrite [h] at this
      assumption
    rewrite [h_eq] at this
    rewrite [this]
    simp

theorem execution_from_state_prec_program_3_1 (R : Nat) (v : VectNat (n + 1)) :
    execution_from_state (R :: v.head :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList) (match (generalizing := false) n with | 0 => CLEAR X 1 | n + 1 => CLEAR X 1 ++ clear_X_j_to_X_n_plus_j 3 n)
        = R :: 0 :: 0 :: List.zeros n ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList := by
  cases n
  case zero =>
    simp [execution_from_state, clear_value]
  case succ n =>
    simp [concat_is_seq_execution, execution_from_state, clear_value]
    repeat rewrite [←List.append_assoc]
    repeat rewrite [clear_X_succ]
    rewrite [List.append_assoc]
    have : highest_var (clear_X_j_to_X_n_plus_j 0 n) ≤ n := by simp [highest_var_clear]
    rewrite [execution_from_state_gt_highest_append v.tail this]
    rewrite [clear_X_lemma]
    rewrite [←List.append_assoc]
    rw [append_zeros_addition (n + 1) ((offset_pr f_h g_h - (n + 1 + 2))) ((n + 1 + (offset_pr f_h g_h - (n + 1 + 2)))) (by simp)]

theorem execution_from_state_prec_program_3_2 (R : Nat) (v : VectNat (n + 1)) :
    execution_from_state (R :: 0 :: 0 :: List.zeros n ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList) (setup_X_j_to_X_n_plus_j (offset_pr f_h g_h) 1 n)
        = R :: v.toList ++ List.zeros (offset_pr f_h g_h - (n + 1)) ++ v.toList := by
  have h_eq : offset_pr f_h g_h = offset_pr f_h g_h - 1 + 1 := by
    suffices h : offset_pr f_h g_h ≥ 1 from (Nat.sub_add_cancel h).symm
    simp_arith [offset_pr ]
  rewrite [h_eq]
  repeat rewrite [List.cons_append]
  rewrite [setup_X_succ]
  repeat rewrite [←List.cons_append]
  rewrite [←zeros_succ, ←zeros_succ, List.zeros_concat, h_eq.symm]
  simp
  rewrite [←List.cons_append, ←zeros_succ]
  have : offset_pr f_h g_h - (n + 2) + 1 = offset_pr f_h g_h - (n + 1) := by
    have : n + 2 = (n + 1) + 1 := rfl
    rewrite [this, Nat.sub_add_eq]
    suffices h : offset_pr f_h g_h - (n + 1) ≥ 1 from Nat.sub_add_cancel h
    have : offset_pr f_h g_h ≥ n + 2 := by simp [offset_pr ]
    have := Nat.sub_le_sub_right this (n + 1)
    have h : n + 2 - (n + 1) = 1 := by simp_arith
    rewrite [h] at this
    assumption
  rewrite [this]
  have : (List.zeros (offset_pr f_h g_h - (n + 1))).length = offset_pr f_h g_h - (n + 1) := by simp
  have h_l := lemma_setup (offset_pr f_h g_h - (n + 1)) n ⟨List.zeros (offset_pr f_h g_h - (n + 1)), this⟩ v
  have : n + (offset_pr f_h g_h - (n + 1)) = offset_pr f_h g_h - 1 := by
    rewrite [Nat.add_comm n 1]
    rewrite [Nat.add_comm, Nat.sub_add_eq]
    suffices h : offset_pr f_h g_h - 1 ≥ n from Nat.sub_add_cancel h
    have : offset_pr f_h g_h ≥ n + 1 := by simp [offset_pr ]
    have := Nat.sub_le_sub_right this 1
    rewrite [Nat.add_sub_cancel] at this
    assumption
  rewrite [this] at h_l
  dsimp at h_l
  repeat rewrite [List.append_assoc] at h_l
  rw [h_l]

theorem execution_from_state_prec_program_3_3 (R : Nat) (v : VectNat (n + 1)) :
    execution_from_state (R :: v.toList ++ List.zeros (offset_pr f_h g_h - (n + 1)) ++ v.toList) (clear_Z_0_to_Z_n (offset_pr f_h g_h + 1) n)
        = R :: v.toList ++ List.zeros (offset_pr f_h g_h) := by
  have : (R :: v.toList ++ List.zeros (offset_pr f_h g_h - (n + 1))).length = offset_pr f_h g_h + 1 := by simp [offset_pr ]
  rewrite [clear_Z_lemma v this]
  simp [offset_pr ]

theorem execution_from_state_prec_program_3 (v : VectNat (n + 1)) :
  execution_from_state ((v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) :: v.head :: 0 :: v.tail.toList ++ List.zeros (offset_pr f_h g_h - (n + 2)) ++ v.toList) (prec_program_3 f_h g_h)
    = (v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) :: v.toList ++ List.zeros (offset_pr f_h g_h) := by
  dsimp [prec_program_3]
  repeat rewrite [concat_is_seq_execution]
  simp [execution_from_state]
  repeat rewrite [←List.cons_append]
  repeat rewrite [←List.append_assoc]
  rw [execution_from_state_prec_program_3_1, execution_from_state_prec_program_3_2,
    execution_from_state_prec_program_3_3]

theorem execution_from_state_prec_program (v : VectNat (n + 1)) :
    execution_from_state (0 :: v.toList ++ 0 :: List.zeros (offset_pr f_h g_h - (n + 2)) ++ 0 :: List.zeros n) (prec_program f_h g_h)
      = (v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) :: v.toList ++ List.zeros (offset_pr f_h g_h) := by
  dsimp [prec_program]
  repeat rewrite [concat_is_seq_execution]
  simp [execution_from_state]
  repeat rewrite [←List.cons_append]
  repeat rewrite [←List.append_assoc]
  rw [execution_from_state_prec_program_1, execution_from_state_prec_program_2,
   execution_from_state_prec_program_3]

theorem prec_is_loop_computable_cleanly : loop_computable_cleanly f
    → loop_computable_cleanly g
    → loop_computable_cleanly fun v : VectNat (n + 1) =>
      v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail) := by
  intro ⟨p_f, f_h⟩ ⟨p_g, g_h⟩
  exists prec_program f_h g_h
  intro v
  rewrite [prec_program_highest_var]
  have : offset_pr f_h g_h + 1 + n - (n + 1) = offset_pr f_h g_h := by
    rewrite [Nat.add_assoc, Nat.add_comm 1 n]
    rw [Nat.add_sub_cancel]
  rewrite [this]
  have : offset_pr f_h g_h = offset_pr f_h g_h - (n + 2) + (n + 1) + 1 := by
    rewrite [Nat.add_assoc]
    suffices h : offset_pr f_h g_h ≥ n + 2 from (Nat.sub_add_cancel h).symm
    simp [offset_pr ]
  have : init_state v ++ List.zeros (offset_pr f_h g_h)
      = 0 :: v.toList ++ 0 :: List.zeros (offset_pr f_h g_h - (n + 2)) ++ 0 :: List.zeros n := by
    dsimp [init_state]
    rewrite [this]
    rewrite [zeros_succ]
    rewrite [←append_zeros_addition (offset_pr f_h g_h - (n + 2)) (n + 1) (offset_pr f_h g_h - (n + 2) + (n + 1)) rfl]
    rewrite [zeros_succ]
    simp
  rewrite [this]
  rw [execution_from_state_prec_program]

end prec_is_loop_computable_cleanly_proof

section comp_is_loop_computable_cleanly_proof

-- We introduce a section as to delimit the proof, but there won't be any
-- variable declaration, to make everything more explicit.

-- variable
--   {n m: Nat}
--   {f : VectNat n → Nat}
--   (g : Fin n → VectNat m → Nat)
--   (f_h : cleanly_computes p_f f)
--   (p_g : Fin n → Program)
--   (g_h : ∀ i, cleanly_computes (p_g i) (g i))

def highest_var_p_g {n : Nat} (p_g : Fin n → Program) : Nat := match n with
  | 0 => 0
  | n + 1 =>
    let p_g_succ_n := p_g ⟨n, Nat.lt_succ_self n⟩
    let p_g' : Fin n → Program
      | ⟨k, p⟩ => p_g ⟨k, Nat.lt_trans p (Nat.lt_succ_self n)⟩
    max (highest_var p_g_succ_n) (highest_var_p_g p_g')

-- -- A bit different from offset_prec. It needs to know m, n, p_g and p_f. It
-- -- takes three explicit arguments: m, p_f and p_g (from which n is obtained).
def offset_comp (m : Nat) (p_g : Fin n → Program) (p_f : Program) : Nat
  := max (max n m) (max (highest_var p_f) (highest_var_p_g p_g))

theorem highest_var_p_g_ge_highest_var_p_g_i {p_g : Fin n → Program} :
    ∀ i : Fin n, highest_var (p_g i) ≤ highest_var_p_g p_g := by
  induction n
  case zero =>
    intro ⟨_, _⟩
    contradiction
  case succ n n_ih =>
    intro ⟨k, p⟩
    let p_g' : Fin n → Program
      | ⟨k, p⟩ => p_g ⟨k, Nat.lt_trans p (Nat.lt_succ_self n)⟩
    have : highest_var_p_g p_g = max (highest_var (p_g ⟨n, Nat.lt_succ_self n⟩)) (highest_var_p_g p_g') := by dsimp [highest_var_p_g]
    rewrite [this]
    cases (Nat.decEq k n)
    case isTrue h =>
      have : (⟨k, p⟩ : Fin (n + 1)) = ⟨n, Nat.lt_succ_self n⟩ := Fin.eq_of_val_eq h
      rewrite [this]
      exact Nat.le_max_left _ _
    case isFalse h =>
      suffices h' : highest_var (p_g ⟨k, p⟩) ≤ highest_var_p_g p_g' from by simp [h']
      have p' : k < n := by
        cases (Nat.decLt k n)
        case isTrue h =>
          exact h
        case isFalse h' =>
          rewrite [Nat.not_lt_eq k n] at h'
          have : k ≤ n := Nat.le_of_lt_succ p
          have : k = n := Nat.le_antisymm this h'
          contradiction
      have : p_g ⟨k, p⟩ = p_g' ⟨k, p'⟩ := by dsimp
      rewrite [this]
      exact n_ih ⟨k, p'⟩

-- -- 0 :: v.toList ++ List.zeros (offset_comp m p_g p_f - m) ++ List.zeros m ++ List.zeros n

-- -- Store X i
def execution_from_state_comp_store_succ_m_inputs (m : Nat) (p_g : Fin n → Program) (p_f : Program) (v : VectNat (m + 1)) :
    execution_from_state (0 :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ List.zeros (m + 1) ++ List.zeros n)
    (store_X_1_to_X_succ_n (offset_comp (m + 1) p_g p_f + 1) m)
      = 0 :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ v.toList ++ List.zeros n := by
  sorry

def compute_store_g_i (p_g : Fin n → Program) (offset_store : Nat) (i : Fin n) : Program :=
  p_g i ++ (X (offset_store + 1 + i) += X 0) ++ CLEAR X 0

-- TODO: verify
def compute_store_all_succ_n_g (n m : Nat) (p_g : Fin (n + 1) → Program) (p_f : Program) (offset_store : Nat) : Program :=
  match n with
  | 0 => compute_store_g_i p_g offset_store 0
  | n + 1 => compute_store_g_i p_g offset_store 0 ++ compute_store_all_succ_n_g n m (fun i => p_g i.succ) p_f offset_store

def execution_from_state_comp_compute_store_succ_n_g (m : Nat) (g : Fin (n + 1) → VectNat m → Nat) (p_g : Fin (n + 1) → Program)
    (p_f : Program) (v : VectNat m) :
    execution_from_state (0 :: v.toList ++ List.zeros (offset_comp m p_g p_f - m) ++ v.toList ++ List.zeros (n + 1))
    (compute_store_all_succ_n_g n m p_g p_f (offset_comp m p_g p_f + m))
      = 0 :: v.toList ++ List.zeros (offset_comp m p_g p_f - m) ++ v.toList ++ (Vector.ofFn (fun i => g i v)).toList := by
  sorry

def execution_from_state_comp_clear_succ_m_inputs (m : Nat) (p_g : Fin n → Program) (p_f : Program) (v : VectNat (m + 1)) :
    execution_from_state (0 :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ v.toList ++ xs)
      (clear_X_j_to_X_n_plus_j 1 m)
        = 0 :: List.zeros (offset_comp (m + 1) p_g p_f) ++ v.toList ++ xs := by
  sorry

def execution_from_state_comp_setup_succ_n_inputs (m : Nat) (g : Fin (n + 1) → VectNat m → Nat) (p_g : Fin (n + 1) → Program)
    (p_f : Program) (v : VectNat m) :
    execution_from_state (0 :: List.zeros (offset_comp m p_g p_f) ++ v.toList ++ (Vector.ofFn (fun i => g i v)).toList)
    (setup_X_j_to_X_n_plus_j (offset_comp m p_g p_f + m) 1 n)
      = 0 :: (Vector.ofFn (fun i => g i v)).toList ++ List.zeros (offset_comp m p_g p_f - (n + 1)) ++ v.toList ++ (Vector.ofFn (fun i => g i v)).toList := by
  sorry

def execution_from_state_comp_clear_succ_n_z (m : Nat) (g : Fin (n + 1) → VectNat m → Nat) (p_g : Fin (n + 1) → Program)
    (p_f : Program) (v : VectNat m) :
    execution_from_state (0 :: (Vector.ofFn (fun i => g i v)).toList ++ List.zeros (offset_comp m p_g p_f - (n + 1)) ++ v.toList ++ (Vector.ofFn (fun i => g i v)).toList)
    (clear_Z_0_to_Z_n (offset_comp m p_g p_f + m + 1) n)
      = 0 :: (Vector.ofFn (fun i => g i v)).toList ++ List.zeros (offset_comp m p_g p_f - (n + 1)) ++ v.toList ++ List.zeros (n + 1) := by
  sorry

def execution_from_state_comp_execute_p_f (g : Fin (n + 1) → VectNat m → Nat) (p_g : Fin (n + 1) → Program)
    (f_h : cleanly_computes p_f f) :
    execution_from_state (0 :: (Vector.ofFn (fun i => g i v)).toList ++ List.zeros (offset_comp m p_g p_f - n) ++ v.toList ++ List.zeros n)
      p_f =  f (Vector.ofFn (fun i => g i v)) :: (Vector.ofFn (fun i => g i v)).toList ++ List.zeros (offset_comp m p_g p_f - n) ++ v.toList ++ List.zeros n := by
  sorry

def execution_from_state_comp_clear_succ_n_inputs (m : Nat) (g : Fin (n + 1) → VectNat m → Nat) (p_g : Fin (n + 1) → Program)
    (p_f : Program) (v : VectNat m) :
    execution_from_state (x :: (Vector.ofFn (fun i => g i v)).toList ++ List.zeros (offset_comp m p_g p_f - (n + 1)) ++ v.toList ++ List.zeros (n + 1))
    (clear_X_j_to_X_n_plus_j 1 n)
      = x :: List.zeros (offset_comp m p_g p_f) ++ v.toList ++ List.zeros (n + 1) := by
  sorry

def execution_from_state_comp_setup_succ_m_inputs (m : Nat) (p_g : Fin n → Program) (p_f : Program) (v : VectNat (m + 1)) :
    execution_from_state (x :: List.zeros (offset_comp (m + 1) p_g p_f) ++ v.toList ++ List.zeros n)
    (setup_X_j_to_X_n_plus_j (offset_comp (m + 1) p_g p_f) 1 m)
      = x :: v.toList ++ List.zeros (offset_comp (m + 1) p_g p_f - (m + 1)) ++ v.toList ++ List.zeros n := by
  sorry

def execution_from_state_comp_clear_succ_m_z (m : Nat) (p_g : Fin (n + 1) → Program) (p_f : Program) (v : VectNat m) :
    execution_from_state (x :: v.toList ++ List.zeros (offset_comp m p_g p_f - m) ++ v.toList ++ List.zeros (n + 1))
    (clear_Z_0_to_Z_n (offset_comp m p_g p_f + 1) m)
      = x :: v.toList ++ List.zeros (offset_comp m p_g p_f - m) ++ List.zeros ((n + 1) + m) := by
  sorry

-- TODO: check if m = 0 is needed
-- This was hard
def comp_program (g : Fin n → VectNat m → Nat) (_ : cleanly_computes p_f f) (p_g : Fin n → Program)
    (_ : ∀ i, cleanly_computes (p_g i) (g i)) : Program := match n with
  | 0 => match m with
    | 0 => p_f
    | m + 1 =>
         store_X_1_to_X_succ_n (offset_comp (m + 1) p_g p_f + 1) m
      ++ clear_X_j_to_X_n_plus_j 1 m
      ++ p_f
      ++ setup_X_j_to_X_n_plus_j (offset_comp (m + 1) p_g p_f) 1 m
      ++ clear_Z_0_to_Z_n (offset_comp m p_g p_f + 1) m
  | n + 1 => match m with
    | 0 =>
         compute_store_all_succ_n_g n m p_g p_f (offset_comp m p_g p_f + m)
      ++ setup_X_j_to_X_n_plus_j (offset_comp m p_g p_f + m) 1 n
      ++ clear_Z_0_to_Z_n (offset_comp m p_g p_f + m + 1) n
      ++ p_f
      ++ clear_X_j_to_X_n_plus_j 1 n
    | m + 1 =>
         store_X_1_to_X_succ_n (offset_comp (m + 1) p_g p_f + 1) m
      ++ compute_store_all_succ_n_g n m p_g p_f (offset_comp m p_g p_f + m)
      ++ clear_X_j_to_X_n_plus_j 1 m
      ++ setup_X_j_to_X_n_plus_j (offset_comp m p_g p_f + m) 1 n
      ++ clear_Z_0_to_Z_n (offset_comp m p_g p_f + m + 1) n
      ++ p_f
      ++ clear_X_j_to_X_n_plus_j 1 n
      ++ setup_X_j_to_X_n_plus_j (offset_comp (m + 1) p_g p_f) 1 m
      ++ clear_Z_0_to_Z_n (offset_comp m p_g p_f + 1) m


-- 1. def execution_from_state_comp_store_succ_m_inputs
-- 2. def execution_from_state_comp_compute_store_succ_n_g
-- 3. def execution_from_state_comp_clear_succ_m_inputs
-- 4. def execution_from_state_comp_setup_succ_n_inputs
-- 5. def execution_from_state_comp_clear_succ_n_z
-- 6. def execution_from_state_comp_execute_p_f
-- 7. def execution_from_state_comp_clear_succ_n_inputs
-- 8. def execution_from_state_comp_setup_succ_m_inputs
-- def execution_from_state_comp_clear_succ_m_z

-- theorem comp_is_loop_computable_cleanly (g : Fin n → VectNat m → Nat) :
--       loop_computable_cleanly f
--     → (∀ i, loop_computable_cleanly (g i))
--     → loop_computable_cleanly fun a => f (Vector.ofFn fun i => g i a) := by
--   intro ⟨p_f, f_h⟩ g_h
--   have ⟨p_g, g_h⟩ := forall_exists_function g g_h

  -- sorry

end comp_is_loop_computable_cleanly_proof


/-
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

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

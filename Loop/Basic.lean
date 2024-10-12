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

theorem comp_is_loop_computable_cleanly (g : Fin n → VectNat m → Nat) :
      loop_computable_cleanly f
    → (∀ i, loop_computable_cleanly (g i))
    → loop_computable_cleanly fun a => f (Mathlib.Vector.ofFn fun i => g i a) := by
  sorry

theorem prec_is_loop_computable_cleanly {f : VectNat n → Nat}
    {g : VectNat (n + 2) → Nat} : loop_computable_cleanly f
    → loop_computable_cleanly g
    → loop_computable_cleanly fun v : VectNat (n + 1) =>
      v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail) := by
  intro ⟨p_f, f_h⟩ ⟨p_g, g_h⟩

  -- Definitions for the variables that will be used in the program
  let a := highest_var p_f
  let b := highest_var p_g
  let offset := max (n + 2) (max a b)
  let result := offset + 1
  let Z := fun j => offset + 2 + j -- from Z 0 to Z n

  -- Part I: construction of the program

  -- Step 1: compute f of the last n inputs and store the result in the
  -- 'result' variable

  -- -- 1.1: Store inputs
  -- Note: defined using the recursor instead of 'let rec' construct. This
  -- allows us to expand the defintion and prove prove properties about the
  -- function
  let store_X_1_to_X_succ_n : Nat → Program := Nat.rec
    (X (Z 0) += X 1)
    fun n p_n => p_n ++ X (Z (n + 1)) += X (n + 2)

  let p_1_1 := store_X_1_to_X_succ_n n

  -- -- 1.2: Clear inputs
  let clear_X_j_to_X_n_plus_j (j : Nat) : Nat → Program := Nat.rec
    (CLEAR X j)
    fun n p_n => p_n ++ CLEAR X ((n + 1) + j)

  let p_1_2 := clear_X_j_to_X_n_plus_j 1 n

  -- -- 1.3. Setup inputs and execute f
  let setup_X_j_to_X_n_plus_j (j : Nat) : Nat → Program := Nat.rec
    (X j += X (Z 1))
    fun n p_n => p_n ++ X ((n + 1) + j) += X (Z (n + 2))

  let p_1_3 := match n with
    | 0 => p_f
    | n + 1 => setup_X_j_to_X_n_plus_j 1 n ++ p_f

  -- -- 1.4. Store result
  let p_1_4 := X result += X 0

  -- -- 1.5. Clear X 0
  let p_1_5 := CLEAR X 0

  let p_1 := p_1_1 ++ p_1_2 ++ p_1_3 ++ p_1_4 ++ p_1_5


  -- Step 2: compute g counter number of times, for each recursive step

  -- 2.1: Clear inputs
  let p_2_1 := clear_X_j_to_X_n_plus_j 1 (n + 1)

  -- 2.2: Setup X 2
  let p_2_2 := X 2 += X result

  -- 2.3: Setup inputs and execute_p_g
  let p_2_3 : Program := match n with
    | 0 => p_g
    | n + 1 => setup_X_j_to_X_n_plus_j 3 n ++ p_g

  -- 2.4: Store result
  let p_2_4 := CLEAR X result ++ X result += X 0

  -- 2.5: Clear X 0
  let p_2_5 := CLEAR X 0

  -- 2.6: Increment X 1
  let p_2_6 := INC X 1

  -- 2.7: Loop
  let loop_inner := p_2_2 ++ p_2_3 ++ p_2_4 ++ p_2_5 ++ p_2_6
  let p_2_7 := LOOP X (Z 0) DO loop_inner END

  let p_2 := p_2_1 ++ p_2_7


  -- -- Step 3: Clean up

  -- -- 3.1: Setup X 0
  let p_3_1 := X 0 += X result

  -- -- 3.2: Clear inputs
  let p_3_2 := clear_X_j_to_X_n_plus_j 1 (n + 1)

  -- -- 3.3: Setup inputs
  let p_3_3 : Program := match n with
    | 0 => X 1 += X (Z 0)
    | n + 1 => X 1 += X (Z 0) ++ setup_X_j_to_X_n_plus_j 2 n

  -- -- 3.4: Clear result
  let p_3_4 := CLEAR X result

  -- -- 3.5: Clear Z j
  let clear_Z_0_to_Z_n : Nat → Program := Nat.rec
    (CLEAR X (Z 0))
    fun n p_n => p_n ++ CLEAR X (Z (n + 1))

  let p_3_5 : Program := clear_Z_0_to_Z_n n

  let p_3 := p_3_1 ++ p_3_2 ++ p_3_3 ++ p_3_4 ++ p_3_5

  -- Final program
  let p := p_1 ++ p_2 ++ p_3
  exists p

  intro v

  -- Part II: rewriting to analyise the program more easily
  have highest_var_store (n : Nat) : highest_var (store_X_1_to_X_succ_n n) = Z n := by
    induction n
    case zero =>
      simp [highest_var, Z]
    case succ n n_ih =>
      simp [highest_var, n_ih, Z]
      have : offset + 2 + (n + 1) = (n + 2) + offset + 1 := by simp_arith
      rw [this]
      simp_arith

  have highest_var_clear (j n : Nat) : highest_var (clear_X_j_to_X_n_plus_j j n) = j + n := by
    induction n
    case zero =>
      simp [highest_var]
    case succ n n_ih =>
      simp_arith [highest_var, n_ih]

  have highest_var_setup (j n : Nat) : highest_var (setup_X_j_to_X_n_plus_j j n) = Z n := by
    -- NOT TRUE! j ≤ n + 2
    sorry

  have highest_var_clear_Z (n : Nat) : highest_var (clear_Z_0_to_Z_n n) = Z n := by
    induction n
    case zero =>
      simp [highest_var]
    case succ n n_ih =>
      simp [highest_var, n_ih]
      simp_arith [Z]

  have highest_var_p_1 : highest_var p_1 = Z n := by
    simp [p_1, concat_is_seq_execution, highest_var]
    sorry

  have highest_var_p_2 : highest_var p_2 = Z n := by
    simp [p_2, concat_is_seq_execution, highest_var]
    sorry

  have highest_var_p_3 : highest_var p_3 = Z n := by
    sorry

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

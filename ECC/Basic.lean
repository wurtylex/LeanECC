/-
Copyright (c) 2026 wurtylex (Anthony Chang). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Chai, Erin Jaen, wurtylex (Anthony Chang) 
-/

module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
(Doc String that we happen to need fill this in later)
# Typeclasses for codes

In this file we define #TODO
-/

@[expose] public section

variable (α : Type*) [Fintype α] (n : ℕ)

/-- A code of blocklength n over α is a subset of α^n. -/
def Code : Type _ := Set (Fin n → α)

namespace Code
/-- The alphabet size. -/
def q : ℕ := Fintype.card α

/-- The dimension of the code C, is log_q(|C|) -/
noncomputable def dim (C : Code α n) : ℝ := Real.logb (q α) C.ncard

/-- The rate of Code C is k / n where k is the dimension of C (note that n = 0 then rate is 0) -/
noncomputable def rate (C : Code α n) : ℝ := C.dim / n

/-- Dimension of a code is at most its blocklength -/
lemma dim_le_n (C : Code α n) : C.dim ≤ n := by
  by_cases hq : 2 ≤ Fintype.card α
  · -- q ≥ 2
    have hcard : C.ncard ≤ Fintype.card α^n := by
      have h := Set.ncard_le_ncard (Set.subset_univ C)
      rwa [Set.ncard_univ, Nat.card_eq_fintype_card,
           Fintype.card_fun, Fintype.card_fin] at h
    unfold Code.dim Code.q
    rcases Nat.eq_zero_or_pos C.ncard with h0 | hpos
    · simp [h0]
    · rw [Real.logb_le_iff_le_rpow (by exact_mod_cast hq) (by exact_mod_cast hpos),
          Real.rpow_natCast]
      exact_mod_cast hcard
  · -- q < 2
    have hdim : C.dim = 0 := by
      unfold Code.dim Code.q
      have : Fintype.card α = 0 ∨ Fintype.card α = 1 := by omega
      rcases this with h | h <;> rw [h] <;>
        simp [Real.logb_zero_left, Real.logb_one_left]
    rw [hdim];
    positivity

/-- Rate is at most 1 -/
lemma rate_le_one (C : Code α n) : C.rate ≤ 1 :=
  div_le_one_of_le₀ C.dim_le_n (by positivity)

end Code

namespace Function

/-- Equivalent description of a code, I assume that the Code has to be the same size though -/
structure EncodingFunction (C : Code α n) where
  toFun : Fin (Set.ncard C) → (Fin n → α)
  range : Set.range toFun = C
  injective : Function.Injective toFun

end Function

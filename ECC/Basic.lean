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
public import Mathlib.LinearAlgebra.Matrix.Rank

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

end -- close @[expose] public section

/-!
## Linear Codes via Generator and Parity-Check Matrices

A **linear code** of blocklength `n` over a field `F` is a subspace of `F^n`.
Two standard matrix presentations exist:

* **Generator matrix** `G : F^{k×n}` — the code is the row space of `G`,
  i.e., the image of `v ↦ v ᵥ* G`.
* **Parity-check matrix** `H : F^{m×n}` — the code is the right null space of `H`,
  i.e., the kernel of `v ↦ H *ᵥ v`.
-/

namespace LinearCode

open Matrix

variable {F : Type*} [Field F] {n : ℕ}

/-- The linear code with generator matrix `G : F^{k×n}` is the image of the
    row-multiplication linear map `v ↦ v ᵥ* G`.  A codeword is any `F`-linear
    combination of the rows of `G`. -/
def ofGeneratorMatrix {k : ℕ} (G : Matrix (Fin k) (Fin n) F) :
    Subspace F (Fin n → F) :=
  LinearMap.range (Matrix.vecMulLinear G)

/-- Membership in the generator-matrix code: `c` is a codeword iff it is
    `v ᵥ* G` for some coefficient vector `v`. -/
@[simp]
theorem mem_ofGeneratorMatrix {k : ℕ} {G : Matrix (Fin k) (Fin n) F}
    {c : Fin n → F} :
    c ∈ ofGeneratorMatrix G ↔ ∃ v : Fin k → F, v ᵥ* G = c := by
  simp only [ofGeneratorMatrix, LinearMap.mem_range, Matrix.vecMulLinear_apply]

/-- The linear code with parity-check matrix `H : F^{m×n}` is the kernel of
    the matrix-vector linear map `v ↦ H *ᵥ v`.  A codeword must satisfy
    every parity-check equation imposed by the rows of `H`. -/
def ofParityCheckMatrix {m : ℕ} (H : Matrix (Fin m) (Fin n) F) :
    Subspace F (Fin n → F) :=
  LinearMap.ker (Matrix.mulVecLin H)

/-- Membership in the parity-check code: `c` is a codeword iff `H *ᵥ c = 0`. -/
@[simp]
theorem mem_ofParityCheckMatrix {m : ℕ} {H : Matrix (Fin m) (Fin n) F}
    {c : Fin n → F} :
    c ∈ ofParityCheckMatrix H ↔ H *ᵥ c = 0 := by
  simp only [ofParityCheckMatrix, LinearMap.mem_ker, Matrix.mulVecLin_apply]

end LinearCode

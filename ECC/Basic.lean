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
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
(Doc String that we happen to need fill this in later)
# Typeclasses for codes

In this file we define #TODO
-/

@[expose] public section
open scoped ENNReal

variable (α : Type*) [Fintype α] [DecidableEq α] (n : ℕ)

/-- A code of blocklength n over α is a subset of α^n. -/
def Code : Type _ := Set (Fin n → α)

namespace Code
/-- The alphabet size. -/
def q : ℕ := Fintype.card α

/-- We view Code as a set of its codewords. -/
def toSet (C : Code α n) : Set (Fin n → α) := C

/-- Membership by unfolding to set -/
instance : Membership (Fin n → α) (Code α n) :=
  ⟨fun C c => c ∈ C.toSet⟩

/-- The dimension of the code C, is log_q(|C|) -/
noncomputable def dim (C : Code α n) : ℝ := Real.logb (q α) C.ncard

/-- The rate of Code C is k / n where k is the dimension of C (note that n = 0 then rate is 0) -/
noncomputable def rate (C : Code α n) : ℝ := C.dim / n

/-- Minimum distance is hamming distance -/
noncomputable def minDist (C : Code α n) : ℕ∞ :=
  ⨅ c₁ ∈ C, ⨅ c₂ ∈ C, ⨅ _ : c₁ ≠ c₂, (hammingDist c₁ c₂ : ℕ∞)

/-- Relative minimum distiance is minimmum distnace / n -/
noncomputable def relMinDist (C : Code α n) : ℝ≥0∞ :=
  (C.minDist : ℝ≥0∞) / (n : ℝ≥0∞)

/-- The Hamming ball of radius `e` centered at `x`: all words within Hamming distance `e` of `x`. -/
def hammingBall (x : Fin n → α) (e : ℕ) : Set (Fin n → α) :=
  {y | hammingDist x y ≤ e}

omit [Fintype α] in
@[simp]
lemma mem_hammingBall {x y : Fin n → α} {e : ℕ} :
    y ∈ hammingBall α n x e ↔ hammingDist x y ≤ e := Iff.rfl

/-- The volume of a Hamming ball of radius `r` over an alphabet of size `q` with blocklength `n`:
`V_q(n,r) = ∑_{i=0}^r C(n,i) · (q-1)^i`. -/
def hammingVolume (q n r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (r + 1), n.choose i * (q - 1) ^ i

@[simp]
lemma hammingVolume_def (q n r : ℕ) :
    hammingVolume q n r = ∑ i ∈ Finset.range (r + 1), n.choose i * (q - 1) ^ i := rfl

lemma hammingVolume_zero_radius (q n : ℕ) : hammingVolume q n 0 = 1 := by
  simp [hammingVolume]

/-- The volume entropy bound: Vol_q(n,r) ≤ q^(n·H_q(r/n)), where H_q is the q-ary
entropy function (`Real.qaryEntropy q p / Real.log q` converts from nats to log base q). -/
lemma hammingVolume_le_pow_mul_entropy (q n r : ℕ)
    (hq : 2 ≤ q) (hn : 1 ≤ n) (hr : (r : ℝ) / n ≤ 1 - 1 / q) :
    (hammingVolume q n r : ℝ) ≤
      (q : ℝ) ^ ((n : ℝ) * Real.qaryEntropy q ((r : ℝ) / n) / Real.log q) := by
  sorry

omit [DecidableEq α] in
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

omit [DecidableEq α] in
/-- Rate is at most 1 -/
lemma rate_le_one (C : Code α n) : C.rate ≤ 1 :=
  div_le_one_of_le₀ C.dim_le_n (by positivity)

/-- Maximal Wrt Inclusion if a containing code with same min dist isn't bigger -/
def maximalWrtInclusion (C : Code α n) : Prop :=
  ∀ D : Code α n, C ⊆ D ∧ (C.minDist = D.minDist) → D.ncard ≤ C.ncard

end Code

end -- close @[expose] public section

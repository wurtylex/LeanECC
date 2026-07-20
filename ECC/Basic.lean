/-
Copyright (c) 2026 wurtylex (Anthony Chang). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Chai, Erin Jaen, wurtylex (Anthony Chang)
-/

module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import all Mathlib.Analysis.SpecialFunctions.BinaryEntropy

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

/-- Subset using membership -/
instance : HasSubset (Code α n) :=
  ⟨fun C D => ∀ c ∈ C, c ∈ D⟩

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

omit [Fintype α] in
/-- The minimum distance of any code is at least 1, since it is an infimum
over pairs of distinct codewords (and the empty infimum is ⊤). -/
lemma one_leq_minDist (C : Code α n) : 1 ≤ C.minDist := by
  simp [minDist, Nat.one_le_iff_ne_zero]

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

/-- Fiber cardinality: for a fixed set `S ⊆ [n]` of coordinates, the number of words `y` whose set
of disagreement coordinates with `x` (that is, `{j | x j ≠ y j}`) is exactly `S` is `(q-1)^|S|`.
Such a `y` may take any of `q-1` non-`x j` values on each `j ∈ S` and must equal `x` off `S`. -/
lemma ncard_disagreementFiber (x : Fin n → α) (S : Finset (Fin n)) :
    {y : Fin n → α | (Finset.univ.filter fun j => x j ≠ y j) = S}.ncard = (q α - 1) ^ S.card := by
  -- Reduce the `ncard` of the fiber to a `Finset.card`.
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
  -- The fiber is exactly the words that equal `x` off `S` and differ from `x` on `S`,
  -- i.e. an element of `∏ j, (if j ∈ S then [q]∖{x j} else {x j})`.
  have hset : (Finset.univ.filter fun y : Fin n → α =>
      (Finset.univ.filter fun j => x j ≠ y j) = S)
      = Fintype.piFinset fun j => if j ∈ S then Finset.univ.erase (x j) else {x j} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    -- Per-coordinate reading of membership in the pi-finset.
    have key : ∀ j : Fin n,
        (y j ∈ if j ∈ S then Finset.univ.erase (x j) else {x j}) ↔ (x j ≠ y j ↔ j ∈ S) := by
      intro j
      by_cases hj : j ∈ S
      · rw [if_pos hj, Finset.mem_erase]
        simp only [Finset.mem_univ, and_true, hj, iff_true]
        exact ne_comm
      · rw [if_neg hj, Finset.mem_singleton]
        simp only [hj, iff_false, not_not]
        exact eq_comm
    -- `supp y = S` unfolds to the same per-coordinate condition.
    rw [Finset.ext_iff]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, key]
  -- Count the fiber: `∏ j, |if j ∈ S then [q]∖{x j} else {x j}| = (q-1)^|S|`.
  rw [hset, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Finset.card_singleton]
  rw [Fintype.prod_ite_mem, Finset.prod_const]
  rfl

/-- Sphere cardinality: the number of words at Hamming distance exactly `i` from `x`
is `C(n,i)·(q-1)^i`. -/
lemma ncard_hammingSphere (x : Fin n → α) (i : ℕ) :
    {y : Fin n → α | hammingDist x y = i}.ncard = n.choose i * (q α - 1) ^ i := by
  -- Reduce the `ncard` of the sphere to a `Finset.card` of a filter of `univ`.
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
  -- Partition the sphere by each word's set of disagreement coordinates
  -- `supp y = {j | x j ≠ y j}`, a size-`i` subset of `[n]` (its size is `hammingDist x y`).
  have hmaps : ((Finset.univ.filter fun y : Fin n → α => hammingDist x y = i : Finset _) :
      Set (Fin n → α)).MapsTo (fun y => Finset.univ.filter fun j => x j ≠ y j)
      ((Finset.univ : Finset (Fin n)).powersetCard i) := by
    intro y hy
    rw [Finset.mem_coe, Finset.mem_filter] at hy
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.filter_subset _ _, hy.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  -- Each fiber (words with a fixed disagreement set `S`, `|S| = i`) has `(q-1)^i` elements,
  -- and there are `C(n,i)` choices of `S`.
  trans ∑ _S ∈ (Finset.univ : Finset (Fin n)).powersetCard i, (q α - 1) ^ i
  · apply Finset.sum_congr rfl
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    obtain ⟨_, hScard⟩ := hS
    -- On the disagreement fiber for `S` the distance filter `= i` is automatic (since `|S| = i`),
    -- so the fiber coincides with the one counted by `ncard_disagreementFiber`.
    rw [Finset.filter_filter]
    have hcongr : (Finset.univ.filter fun y : Fin n → α =>
        hammingDist x y = i ∧ (Finset.univ.filter fun j => x j ≠ y j) = S)
        = Finset.univ.filter fun y : Fin n → α =>
          (Finset.univ.filter fun j => x j ≠ y j) = S := by
      apply Finset.filter_congr
      intro y _
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      calc hammingDist x y = (Finset.univ.filter fun j => x j ≠ y j).card := rfl
        _ = S.card := by rw [h]
        _ = i := hScard
    rw [hcongr, ← Set.toFinset_setOf, ← Set.ncard_eq_toFinset_card',
      ncard_disagreementFiber, hScard]
  · -- Sum the constant `(q-1)^i` over the `C(n,i)` disagreement sets.
    rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_fin, smul_eq_mul]

/-- A Hamming ball of radius r contains exactly V_q(n,r) words. -/
lemma ncard_hammingBall (x : Fin n → α) (r : ℕ) :
    (hammingBall α n x r).ncard = hammingVolume (q α) n r := by
  -- Reduce the `ncard` of the ball to a `Finset.card` of a filter of `univ`.
  rw [hammingBall, hammingVolume_def, Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
  -- Partition the ball by each word's distance to `x`, which lands in `{0, …, r}`.
  have hmaps : ((Finset.univ.filter fun y : Fin n → α => hammingDist x y ≤ r : Finset _) :
      Set (Fin n → α)).MapsTo (fun y => hammingDist x y) (Finset.range (r + 1)) := by
    intro y hy
    rw [Finset.mem_coe, Finset.mem_filter] at hy
    rw [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le hy.2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  -- The fiber at distance `i ≤ r` is the sphere of radius `i`, counted by `ncard_hammingSphere`.
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hfib : (Finset.univ.filter fun y : Fin n → α => hammingDist x y ≤ r).filter
      (fun y => hammingDist x y = i) = Finset.univ.filter fun y => hammingDist x y = i := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    -- Goal: `hammingDist x y ≤ r ∧ hammingDist x y = i ↔ hammingDist x y = i`.
    -- Since `i ≤ r`, the equality `hammingDist x y = i` already forces `hammingDist x y ≤ r`.
    have hir : i ≤ r := Nat.lt_succ_iff.mp hi
    exact and_iff_right_of_imp fun h => h.trans_le hir
  rw [hfib, ← Set.toFinset_setOf, ← Set.ncard_eq_toFinset_card']
  exact ncard_hammingSphere α n x i

/-- The volume entropy bound: Vol_q(n,r) ≤ q^(n·H_q(r/n)), where H_q is the q-ary
entropy function (`Real.qaryEntropy q p / Real.log q` converts from nats to log base q). -/
lemma hammingVolume_le_pow_mul_entropy (q n r : ℕ)
    (hq : 2 ≤ q) (hn : 1 ≤ n) (hr : (r : ℝ) / n ≤ 1 - 1 / q) :
    (hammingVolume q n r : ℝ) ≤
      (q : ℝ) ^ ((n : ℝ) * Real.qaryEntropy q ((r : ℝ) / n) / Real.log q) := by
  -- r = 0 then Vol_q(n, 0) = 1
  obtain rfl | hr0 := Nat.eq_zero_or_pos r
  · simp
  -- Let r ≥ 1 implies 0 < λ ≤ 1 - 1/q < 1
  set l : ℝ := (r : ℝ) / n with hl
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 : (0 : ℝ) < q := by positivity
  have hl0 : 0 < l := div_pos (by exact_mod_cast hr0) hn0
  have hl1 : l < 1 := hr.trans_lt (sub_lt_self 1 (by positivity))
  have h1l : 0 < 1 - l := sub_pos.mpr hl1
  have hql : (0 : ℝ) < (q : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hq)
  have hrn : r < n := by exact_mod_cast (div_lt_one hn0).mp hl1
  -- Since n * λ = r, the definition of H_q gives
  -- n * H_q(λ) = r * log (q-1) + r * log λ⁻¹ + (n-r) * log (1-λ)⁻¹
  have hnl : (n : ℝ) * l = r := by rw [hl, mul_comm, div_mul_cancel₀ _ hn0.ne']
  have hent : (n : ℝ) * Real.qaryEntropy q l
      = (r : ℝ) * Real.log ((q : ℝ) - 1)
        + ((r : ℝ) * Real.log l⁻¹ + ((n - r : ℕ) : ℝ) * Real.log (1 - l)⁻¹) := by
    simp only [Real.qaryEntropy, Real.binEntropy]
    push_cast [Nat.cast_sub hrn.le]
    rw [← hnl]
    ring
  -- since q > 1, q ^ (x / log q) = exp x
  have hexp : (q : ℝ) ^ ((n : ℝ) * Real.qaryEntropy q l / Real.log q)
      = Real.exp ((n : ℝ) * Real.qaryEntropy q l) := by
    rw [Real.rpow_def_of_pos hq0, mul_comm (Real.log _),
      div_mul_cancel₀ _ (Real.log_pos (by exact_mod_cast hq)).ne']
  -- so exponentiating gives q ^ (n * H_q(λ) / log q) = (q-1)^r / (λ^r * (1-λ)^(n-r))
  have hRHS : Real.exp ((n : ℝ) * Real.qaryEntropy q l)
      = ((q : ℝ) - 1) ^ r / (l ^ r * (1 - l) ^ (n - r)) := by
    rw [hent, Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_nat_mul, Real.exp_log hql, Real.exp_log (inv_pos.mpr hl0),
      Real.exp_log (inv_pos.mpr h1l), inv_pow, inv_pow, ← mul_inv, ← div_eq_mul_inv]
  -- and it suffices to show Vol_q(n,r) * λ^r * (1-λ)^(n-r) ≤ (q-1)^r.
  rw [hexp, hRHS, le_div_iff₀ (by positivity)]
  -- θ ≤ 1 where θ = λ / ((q-1)(1-λ))
  -- λ ≤ (q-1)(1-λ)
  have htheta : l ≤ ((q : ℝ) - 1) * (1 - l) := by
    have h : l * q ≤ (q : ℝ) - 1 :=
      calc l * q ≤ (1 - 1 / (q : ℝ)) * q := mul_le_mul_of_nonneg_right hr hq0.le
        _ = q - 1 := by field_simp
    calc l = l * q - l * ((q : ℝ) - 1) := by ring
      _ ≤ ((q : ℝ) - 1) - l * ((q : ℝ) - 1) := sub_le_sub_right h _
      _ = ((q : ℝ) - 1) * (1 - l) := by ring
  -- ∑_{i=0}^n C(n,i) λ^i (1-λ)^(n-i) = (λ + (1-λ))^n = 1
  have hbinom :
      ∑ i ∈ Finset.range (n + 1), l ^ i * (1 - l) ^ (n - i) * (n.choose i : ℝ) = 1 := by
    rw [← add_pow, add_sub_cancel, one_pow]
  calc (hammingVolume q n r : ℝ) * (l ^ r * (1 - l) ^ (n - r))
      = ∑ i ∈ Finset.range (r + 1),
          (n.choose i : ℝ) * ((q : ℝ) - 1) ^ i * (l ^ r * (1 - l) ^ (n - r)) := by
        rw [hammingVolume_def]
        push_cast [Nat.cast_sub (show 1 ≤ q by omega)]
        rw [Finset.sum_mul]
    -- for each 0 ≤ i ≤ r, since r - i ≥ 0 and θ ≤ 1,
    -- C(n,i) (q-1)^i λ^r (1-λ)^(n-r) ≤ (q-1)^r C(n,i) λ^i (1-λ)^(n-i)
    _ ≤ ∑ i ∈ Finset.range (r + 1),
          ((q : ℝ) - 1) ^ r * (l ^ i * (1 - l) ^ (n - i) * (n.choose i : ℝ)) := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hir : i ≤ r := Finset.mem_range_succ_iff.mp hi
        have h1 : l ^ r = l ^ i * l ^ (r - i) := by rw [← pow_add]; congr 1; omega
        have h2 : (1 - l) ^ (n - i) = (1 - l) ^ (n - r) * (1 - l) ^ (r - i) := by
          rw [← pow_add]; congr 1; omega
        have h3 : ((q : ℝ) - 1) ^ r = ((q : ℝ) - 1) ^ i * ((q : ℝ) - 1) ^ (r - i) := by
          rw [← pow_add]; congr 1; omega
        calc (n.choose i : ℝ) * ((q : ℝ) - 1) ^ i * (l ^ r * (1 - l) ^ (n - r))
            = (n.choose i : ℝ) * ((q : ℝ) - 1) ^ i * (l ^ i * (1 - l) ^ (n - r))
                * l ^ (r - i) := by rw [h1]; ring
          _ ≤ (n.choose i : ℝ) * ((q : ℝ) - 1) ^ i * (l ^ i * (1 - l) ^ (n - r))
                * (((q : ℝ) - 1) * (1 - l)) ^ (r - i) := by gcongr
          _ = ((q : ℝ) - 1) ^ r * (l ^ i * (1 - l) ^ (n - i) * (n.choose i : ℝ)) := by
              rw [h2, h3, mul_pow]; ring
    -- summing over 0 ≤ i ≤ r and extending the sum to 0 ≤ i ≤ n
    _ ≤ ∑ i ∈ Finset.range (n + 1),
          ((q : ℝ) - 1) ^ r * (l ^ i * (1 - l) ^ (n - i) * (n.choose i : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (Nat.succ_le_succ hrn.le)) fun i _ _ ↦ by positivity
    _ = ((q : ℝ) - 1) ^ r := by rw [← Finset.mul_sum, hbinom, mul_one]

omit [DecidableEq α] in
/-- Dimension of a code is at most its blocklength -/
lemma dim_le_n (C : Code α n) : C.dim ≤ n := by
  obtain h0 | hpos := Nat.eq_zero_or_pos C.ncard
  · -- the empty code: `dim C = logb q 0 = 0`
    simp [dim, h0]
  obtain hq | hq := Nat.lt_or_ge (Fintype.card α) 2
  · -- degenerate alphabet: the log base is `0` or `1`, so `dim C = 0`
    rcases (by omega : Fintype.card α = 0 ∨ Fintype.card α = 1) with h | h <;>
      simp [dim, q, h]
  · -- `2 ≤ q`: from `|C| ≤ q ^ n`, take `logb q` of both sides
    have hq1 : (1 : ℝ) < Fintype.card α := by exact_mod_cast hq
    have hcard : (C.ncard : ℝ) ≤ (Fintype.card α : ℝ) ^ n := by
      have h := Set.ncard_le_ncard (Set.subset_univ C)
      simp only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun,
        Fintype.card_fin] at h
      exact_mod_cast h
    calc C.dim ≤ Real.logb (Fintype.card α) ((Fintype.card α : ℝ) ^ n) :=
          Real.logb_le_logb_of_le hq1 (by exact_mod_cast hpos) hcard
      _ = n := by rw [Real.logb_pow, Real.logb_self_eq_one hq1, mul_one]

omit [DecidableEq α] in
/-- Rate is at most 1 -/
lemma rate_le_one (C : Code α n) : C.rate ≤ 1 :=
  div_le_one_of_le₀ C.dim_le_n (by positivity)

/-- Maximal Wrt Inclusion if a containing code with same min dist isn't bigger -/
def maximalWrtInclusion (C : Code α n) : Prop :=
  ∀ D : Code α n, C ⊆ D ∧ (C.minDist = D.minDist) → D ⊆ C

/-- Given a maximal wrt inclusion code C with minimum distance ≤ d,
block length n, and d <= n, the union of hamming balls with radius d-1 around each
element of C cover the universe -/
lemma covers
    (d : ℕ)
    (C : Code α n)
    (h_C_maximal : C.maximalWrtInclusion)
    (h_C_min_dist : C.minDist ≤ d) :
    (⋃ x ∈ C, (hammingBall α n x (d - 1))).ncard = (q α)^n := by sorry

/-- Maximal packing to fill in later -/
lemma maxPacking (C : Code α n) (d : ℕ)
  (h_C_maximal : C.maximalWrtInclusion)
  (h_C_min_dist : C.minDist ≤ d) :
  (q α)^n ≤ C.ncard * hammingVolume (q α) n (d - 1) := by
  /- have h_d_geq_1 : 1 ≤ d := by
    have h1 := (one_leq_minDist α n C).trans h_C_min_dist
    exact_mod_cast h1
  -/
  have hC := Set.toFinite C.toSet
  calc (q α)^n
      -- = |∪ x ∈ C, B(x, d-1)|
      = (⋃ x ∈ C, hammingBall α n x (d - 1)).ncard :=
        (covers α n d C h_C_maximal h_C_min_dist).symm
      -- = |⋃ x ∈ C.toFinset, B(x, d-1)|
    _ = (⋃ x ∈ hC.toFinset, hammingBall α n x (d - 1)).ncard := by
        simp only [Set.Finite.mem_toFinset]; rfl
      -- ≤ ∑ x ∈ C, |B(x, d-1)|
    _ ≤ ∑ x ∈ hC.toFinset, (hammingBall α n x (d - 1)).ncard :=
        hC.toFinset.set_ncard_biUnion_le _
      -- = ∑ x ∈ C, Vol_q(n, d-1)
    _ = ∑ _x ∈ hC.toFinset, hammingVolume (q α) n (d - 1) :=
        Finset.sum_congr rfl fun x _ => ncard_hammingBall α n x (d - 1)
      -- = |C| · Vol_q(n, d-1)
    _ = C.ncard * hammingVolume (q α) n (d - 1) := by
        rw [Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card _ hC]
        rfl
end Code

end -- close @[expose] public section

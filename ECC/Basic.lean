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
@[simp] def Code : Type _ := Set (Fin n → α)

namespace Code
/-- The alphabet size. -/
def q : ℕ := Fintype.card α

/-- We view Code as a set of its codewords. -/
def toSet (C : Code α n) : Set (Fin n → α) := C

/-- Membership by unfolding to set -/
@[simp] instance : Membership (Fin n → α) (Code α n) :=
  ⟨fun C c => c ∈ C.toSet⟩

/-- Subset using membership -/
@[simp] instance : HasSubset (Code α n) :=
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

/-- A Hamming ball of radius r contains exactly V_q(n,r) words. -/
lemma ncard_hammingBall (x : Fin n → α) (r : ℕ) :
    (hammingBall α n x r).ncard = hammingVolume (q α) n r := by sorry

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

omit [DecidableEq α] in
/-- The universal set has cardinality (q α)^n -/
lemma ncard_univ_eq_q_pow : (Set.univ : Set (Fin n → α)).ncard = (q α)^n := by
  simp only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, q]

omit [Fintype α] in
/-- A code that is a subset of another must always have a greater than or equal min distance -/
lemma subset_mindist {C D : Code α n} (hsub : C ⊆ D) : D.minDist ≤ C.minDist := by
  unfold minDist
  -- it suffices to bound D.minDist by the distance of each pair of distinct codewords of C
  simp only [le_iInf_iff]
  intro c₁ hc₁ c₂ hc₂ hne
  -- both codewords also lie in D, so the infimum over D is at most their distance
  calc ⨅ x ∈ D, ⨅ y ∈ D, ⨅ _ : x ≠ y, (hammingDist x y : ℕ∞)
      ≤ ⨅ y ∈ D, ⨅ _ : c₁ ≠ y, (hammingDist c₁ y : ℕ∞) := iInf₂_le c₁ (hsub c₁ hc₁)
    _ ≤ ⨅ _ : c₁ ≠ c₂, (hammingDist c₁ c₂ : ℕ∞) := iInf₂_le c₂ (hsub c₂ hc₂)
    _ ≤ (hammingDist c₁ c₂ : ℕ∞) := iInf_le _ hne

omit [Fintype α] in
/-- Any unequal pair of elements of C will have a hamming distance ≥ than C's minDist -/
lemma minDist_le_any_pair {C : Code α n} {c1 : Fin n → α} {c2 : Fin n → α}
    (h_c1_in_C : c1 ∈ C)
    (h_c2_in_C : c2 ∈ C)
    (h_neq : c1 ≠ c2) :
    hammingDist c1 c2 ≥ C.minDist := by
  exact calc ⨅ c₁ ∈ C, ⨅ c₂ ∈ C, ⨅ _ : c₁ ≠ c₂, (hammingDist c₁ c₂ : ℕ∞)
    ≤ ⨅ c₂ ∈ C, ⨅ _ : c1 ≠ c₂, (hammingDist c1 c₂ : ℕ∞) :=
      iInf₂_le c1 h_c1_in_C
    _ ≤ ⨅ _ : c1 ≠ c2, (hammingDist c1 c2 : ℕ∞) :=
      iInf₂_le c2 h_c2_in_C
    _ ≤ (hammingDist c1 c2 : ℕ∞) :=
      iInf_le _ h_neq

omit [Fintype α] in
/-- Lower bounds the minimum distance of a code after inserting a new codeword. -/
lemma le_minDist_insert {C : Code α n} {c : Fin n → α} {d_exact : ℕ∞}
    (h_minDist : C.minDist = d_exact)
    (h_dist : ∀ x ∈ C, d_exact ≤ (hammingDist x c : ℕ∞)) :
    d_exact ≤ minDist α n (insert c C.toSet : Set (Fin n → α)) := by
  unfold minDist
  simp only [le_iInf_iff]
  intro c1 hc1 c2 hc2 h_neq
  -- Pattern match on whether c1 and c2 are the new element 'c' or belong to 'C'
  rcases Set.mem_insert_iff.mp hc1 with rfl | h1
  · rcases Set.mem_insert_iff.mp hc2 with rfl | h2
    · exact (h_neq rfl).elim -- c1 and c2 cannot both be c since c1 ≠ c2
    · rw [hammingDist_comm]
      exact h_dist c2 h2
  · rcases Set.mem_insert_iff.mp hc2 with rfl | h2
    · exact h_dist c1 h1
    · -- Both elements are in C
      rw [← h_minDist]
      exact minDist_le_any_pair _ _ h1 h2 h_neq

/-- Given a maximal wrt inclusion code C with distance ≤ d,
the union of hamming balls with radius d-1 around each
element of C cover the universe -/
lemma covers
    (d : ℕ)
    (C : Code α n)
    (h_C_maximal : C.maximalWrtInclusion)
    (h_C_min_dist : C.minDist ≤ d) :
    (⋃ x ∈ C, (hammingBall α n x (d - 1))).ncard = (q α)^n := by
  by_contra! h
  -- Define the exact min distance and assert some basic properties
  let d_exact := C.minDist
  have h_C_min_dist_exact : C.minDist = d_exact := by tauto
  have h_C_min_dist_exact_leq_d : d_exact ≤ d := by
    rw[← h_C_min_dist_exact]
    exact h_C_min_dist
  -- Prove that we have some extraneous element
  have h_extraneous_elt : ∃ (c : Fin n → α), c ∉ (⋃ x ∈ C, hammingBall α n x (d - 1)) := by
    -- "An element is missing implies the set is not the universal set"
    rw [← Set.ne_univ_iff_exists_notMem]
    intro h_union_is_univ
    -- Applying h sets our goal to prove it IS q^n.
    apply h
    rw [h_union_is_univ, ncard_univ_eq_q_pow]
  -- We can create D with the same min distance
  have h_C_plus_extra: ∃ D : Code α n, C ⊆ D ∧ ¬ (D ⊆ C) ∧ D.minDist = d_exact := by
    obtain ⟨c, h_c_not_in_union⟩ := h_extraneous_elt
    -- c must have a hamming distance of at least d from any element of C bc of the balls
    have h_outside_ball_dist (b : Fin n → α) (h_b_in_C : b ∈ C): d_exact ≤ hammingDist b c := by
      unfold hammingBall at h_c_not_in_union
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_le] at h_c_not_in_union
      specialize h_c_not_in_union b h_b_in_C
      have h_hamming_bc_le : d ≤ hammingDist b c := Nat.le_of_pred_lt h_c_not_in_union
      exact h_C_min_dist_exact_leq_d.trans (by exact_mod_cast h_hamming_bc_le)
    let D := insert c C.toSet
    use D
    -- Goal: D.minDist = d_exact
    have h_D_minDist : minDist α n D = d_exact := by
      apply le_antisymm
      -- Part 1: D.minDist ≤ C.minDist (Trivial subset property)
      · apply subset_mindist;
        exact Set.subset_insert c C.toSet
      -- Part 2: D.minDist ≥ d_exact (Using the helper lemma)
      · apply le_minDist_insert _ _ h_C_min_dist_exact h_outside_ball_dist
    rw[h_D_minDist]
    constructor
    · -- Goal 1: C ⊆ insert c C
      exact Set.subset_insert c C
    · constructor
      · -- Goal 2a: ¬(insert c C ⊆ C)
        intro h_sub
        have h_c_in_C : c ∈ C := h_sub c (Set.mem_insert c (toSet α n C))
        apply h_c_not_in_union
        simp only [Code, Set.mem_iUnion, mem_hammingBall]
        exact ⟨c, h_c_in_C, by simp only [hammingDist_self, zero_le]⟩
      · -- Goal 2b: d_exact = d_exact
        trivial
  -- Extract D and its properties
  obtain ⟨D, h_C_sub_D, h_D_not_sub_C, h_D_minDist⟩ := h_C_plus_extra
  -- h_C_maximal dictates that if C ⊆ D and they have the same minDist, then D ⊆ C.
  have h_D_sub_C : D ⊆ C := h_C_maximal D ⟨h_C_sub_D, by rw [h_C_min_dist_exact, h_D_minDist]⟩
  -- This directly contradicts our construction that D is not a subset of C
  exact h_D_not_sub_C h_D_sub_C

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

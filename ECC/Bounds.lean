/-
Copyright (c) 2026 wurtylex (Anthony Chang). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Chai, Erin Jaen, wurtylex (Anthony Chang)
-/

module

public import ECC.Basic

/-!
# Bounds on codes

In this file we prove the Gilbert–Varshamov bound for general codes: existence of a
maximal code of prescribed minimum distance, the combinatorial packing form of the
bound, and the asymptotic rate/entropy form.
-/

@[expose] public section
open scoped ENNReal

variable (α : Type*) [Fintype α] [DecidableEq α] (n : ℕ)

namespace Code

/-- Over an alphabet with at least two symbols, for every d ≤ n there is a pair of
words at Hamming distance exactly d. -/
lemma exists_pair_hammingDist_eq (hq : 2 ≤ q α) {d : ℕ} (hdn : d ≤ n) :
    ∃ x y : Fin n → α, hammingDist x y = d := by
  -- pick two distinct symbols and let the words disagree exactly on the first d coordinates
  obtain ⟨a, b, hab⟩ : ∃ a b : α, a ≠ b :=
    Fintype.exists_pair_of_one_lt_card (Nat.lt_of_lt_of_le one_lt_two hq)
  refine ⟨fun _ => a, fun i => if (i : ℕ) < d then b else a, ?_⟩
  rw [show hammingDist (fun _ => a) (fun i : Fin n => if (i : ℕ) < d then b else a)
      = (Finset.univ.filter fun i : Fin n => a ≠ if (i : ℕ) < d then b else a).card from rfl]
  rw [show (Finset.univ.filter fun i : Fin n => a ≠ if (i : ℕ) < d then b else a)
      = (Finset.range d).attachFin (fun m hm => (Finset.mem_range.mp hm).trans_le hdn) by
    ext i
    by_cases hi : (i : ℕ) < d <;> simp [hi, hab, Finset.mem_attachFin]]
  rw [Finset.card_attachFin, Finset.card_range]

omit [Fintype α] in
/-- The minimum distance of a two-element code is the Hamming distance between the
two codewords. -/
lemma minDist_pair {x y : Fin n → α} (hxy : x ≠ y) :
    minDist α n ({x, y} : Set (Fin n → α)) = hammingDist x y :=
  le_antisymm
    (minDist_le_hammingDist α n (Set.mem_insert x {y}) (Set.mem_insert_of_mem x rfl) hxy)
    (le_minDist α n <| by
      -- each codeword is x or y, and they are distinct, so the pair is {x, y} in some order
      rintro c₁ (rfl | rfl) c₂ (rfl | rfl) hne
      · exact absurd rfl hne
      · exact le_rfl
      · exact_mod_cast (hammingDist_comm _ _).le
      · exact absurd rfl hne)

/-- Among the codes of minimum distance exactly d (a finite nonempty family, seeded by
a pair of words at distance d) there is one that is maximal with respect to inclusion. -/
lemma exists_maximal_code (hq : 2 ≤ q α) {d : ℕ} (hd : 1 ≤ d) (hdn : d ≤ n) :
    ∃ C : Code α n, C.maximalWrtInclusion ∧ C.minDist = (d : ℕ∞) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_hammingDist_eq α n hq hdn
  have hxy' : x ≠ y := by
    rintro rfl
    rw [hammingDist_self] at hxy
    omega
  -- the family of codes of minimum distance exactly d, as a set of sets
  set F : Set (Set (Fin n → α)) := {D | minDist α n D = (d : ℕ∞)} with hF
  have hne : ({x, y} : Set (Fin n → α)) ∈ F := by
    change minDist α n ({x, y} : Set (Fin n → α)) = (d : ℕ∞)
    rw [minDist_pair α n hxy', hxy]
  obtain ⟨C, hCF, hCmax⟩ := (Set.toFinite F).exists_maximal ⟨_, hne⟩
  have hCd : minDist α n C = (d : ℕ∞) := hCF
  refine ⟨C, ?_, hCd⟩
  rintro D ⟨hCD, hdist⟩
  have hDF : D ∈ F := by
    change minDist α n D = (d : ℕ∞)
    rw [← hdist]
    exact hCd
  exact hCmax hDF hCD

/-- Gilbert–Varshamov bound, combinatorial form: for 2 ≤ q and 1 ≤ d ≤ n there
is a code of minimum distance exactly d with q^n ≤ |C| · Vol_q(n, d-1). -/
theorem gilbert_varshamov_card (hq : 2 ≤ q α) {d : ℕ} (hd : 1 ≤ d) (hdn : d ≤ n) :
    ∃ C : Code α n, C.minDist = (d : ℕ∞) ∧
      (q α) ^ n ≤ C.ncard * hammingVolume (q α) n (d - 1) := by
  obtain ⟨C, hmax, hdist⟩ := exists_maximal_code α n hq hd hdn
  exact ⟨C, hdist, maxPacking α n C d hmax hdist.le⟩

/-- Gilbert–Varshamov bound (general codes): for 2 ≤ q, 0 ≤ δ < 1 - 1/q and
block length n ≥ 1 there is a q-ary code of rate at least 1 - H_q(δ) and relative
minimum distance at least δ. Here H_q(δ) = Real.qaryEntropy q δ / Real.log q is the
q-ary entropy converted from nats to log base q. -/
theorem gilbert_varshamov (hq : 2 ≤ q α) (hn : 1 ≤ n) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 - 1 / (q α : ℝ)) :
    ∃ C : Code α n,
      1 - Real.qaryEntropy (q α) δ / Real.log (q α) ≤ C.rate ∧
      ENNReal.ofReal δ ≤ C.relMinDist := by
  have hq1 : (1 : ℝ) < (q α : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hq
  have hq0 : (0 : ℝ) < (q α : ℝ) := one_pos.trans hq1
  have hlogq : 0 < Real.log (q α) := Real.log_pos hq1
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hδ1' : δ < 1 := hδ1.trans (sub_lt_self 1 (by positivity))
  -- the designed distance d = max(⌈δn⌉, 1)
  set d : ℕ := max ⌈δ * n⌉₊ 1 with hd_def
  have hd1 : 1 ≤ d := le_max_right _ _
  have hdn : d ≤ n := by
    apply max_le _ hn
    rw [Nat.ceil_le]
    calc δ * n ≤ 1 * n := mul_le_mul_of_nonneg_right hδ1'.le hn0.le
      _ = n := one_mul _
  have hδnd : δ * n ≤ (d : ℝ) := by
    calc δ * n ≤ (⌈δ * n⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (d : ℝ) := by exact_mod_cast le_max_left _ _
  obtain ⟨C, hCd, hCcard⟩ := gilbert_varshamov_card α n hq hd1 hdn
  -- the packing radius r = d - 1 satisfies r ≤ δn, hence r/n ≤ δ < 1 - 1/q
  set r : ℕ := d - 1 with hr_def
  have hrδn : (r : ℝ) ≤ δ * n := by
    rcases Nat.eq_zero_or_pos ⌈δ * n⌉₊ with h | h
    -- if ⌈δn⌉ = 0 then r = 0 and the claim is just 0 ≤ δn
    · have hr0 : r = 0 := by omega
      rw [hr0, Nat.cast_zero]
      exact mul_nonneg hδ0 hn0.le
    -- otherwise r = ⌈δn⌉ - 1 < ⌈δn⌉, and being below the ceiling means (r : ℝ) < δn
    · have hrlt : r < ⌈δ * n⌉₊ := by omega
      exact (Nat.lt_ceil.mp hrlt).le
  have hrn_le_δ : (r : ℝ) / n ≤ δ := by
    rw [div_le_iff₀ hn0]
    exact hrδn
  have hrange : (r : ℝ) / n ≤ 1 - 1 / (q α : ℝ) := hrn_le_δ.trans hδ1.le
  set H : ℝ := Real.qaryEntropy (q α) ((r : ℝ) / n) with hH
  have hVol : (hammingVolume (q α) n r : ℝ) ≤
      (q α : ℝ) ^ ((n : ℝ) * H / Real.log (q α)) :=
    hammingVolume_le_pow_mul_entropy (q α) n r hq hn hrange
  -- the code is nonempty, so its cardinality is positive
  have hncard : (0 : ℝ) < (C.ncard : ℝ) := by
    exact_mod_cast ncard_pos_of_pow_le α n (by omega) hCcard
  -- packing bound in ℝ: q^n ≤ |C| · Vol_q(n, r)
  have hcardR : (q α : ℝ) ^ (n : ℝ) ≤ (C.ncard : ℝ) * (hammingVolume (q α) n r : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hCcard
  -- hence |C| ≥ q^(n - nH/log q)
  have key : (q α : ℝ) ^ ((n : ℝ) - (n : ℝ) * H / Real.log (q α)) ≤ (C.ncard : ℝ) := by
    rw [Real.rpow_sub hq0, div_le_iff₀ (Real.rpow_pos_of_pos hq0 _)]
    calc (q α : ℝ) ^ (n : ℝ)
        ≤ (C.ncard : ℝ) * (hammingVolume (q α) n r : ℝ) := hcardR
      _ ≤ (C.ncard : ℝ) * (q α : ℝ) ^ ((n : ℝ) * H / Real.log (q α)) :=
          mul_le_mul_of_nonneg_left hVol hncard.le
  -- taking logb, the dimension is at least n - nH/log q
  have hdim : (n : ℝ) - (n : ℝ) * H / Real.log (q α) ≤ C.dim := by
    have hlog := Real.logb_le_logb_of_le hq1 (Real.rpow_pos_of_pos hq0 _) key
    rwa [Real.logb_rpow hq0 hq1.ne'] at hlog
  -- so the rate is at least 1 - H/log q
  have hrate1 : 1 - H / Real.log (q α) ≤ C.rate := by
    change 1 - H / Real.log (q α) ≤ C.dim / n
    rw [le_div_iff₀ hn0]
    calc (1 - H / Real.log (q α)) * n = n - n * H / Real.log (q α) := by ring
      _ ≤ C.dim := hdim
  -- monotonicity of the entropy on [0, 1 - 1/q] turns H(r/n) into H(δ)
  have hmono : H ≤ Real.qaryEntropy (q α) δ :=
    (Real.qaryEntropy_strictMonoOn hq).monotoneOn
      (Set.mem_Icc.mpr ⟨by positivity, hrange⟩)
      (Set.mem_Icc.mpr ⟨hδ0, hδ1.le⟩) hrn_le_δ
  have hrate : 1 - Real.qaryEntropy (q α) δ / Real.log (q α) ≤ C.rate := by
    refine le_trans ?_ hrate1
    gcongr
  -- the relative minimum distance is d/n ≥ δ
  have hdist : ENNReal.ofReal δ ≤ C.relMinDist := by
    change ENNReal.ofReal δ ≤ (C.minDist : ℝ≥0∞) / (n : ℝ≥0∞)
    rw [hCd]
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast (by omega : n ≠ 0)))
      (Or.inl (ENNReal.natCast_ne_top n))]
    calc ENNReal.ofReal δ * (n : ℝ≥0∞)
        = ENNReal.ofReal (δ * n) := by
          rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul hδ0]
      _ ≤ ENNReal.ofReal (d : ℝ) := ENNReal.ofReal_le_ofReal hδnd
      _ = ((d : ℕ∞) : ℝ≥0∞) := by
          rw [ENNReal.ofReal_natCast d]
          exact_mod_cast rfl
  exact ⟨C, hrate, hdist⟩

end Code

end -- close @[expose] public section

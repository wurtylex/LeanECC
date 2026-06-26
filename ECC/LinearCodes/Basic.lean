/-
Copyright (c) 2026 wurtylex (Anthony Chang). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Chai, Erin Jaen, wurtylex (Anthony Chang)
-/

module

public import ECC.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
/-!
Definition of a linear code, as well as it's generator and parity check matrices
-/

@[expose] public section

open Matrix

variable {F : Type*} [Field F] [Fintype F] {n : ℕ}

/-- Note that this is proper definition
finite field can only contain a number of elements equal to a prime power -/
structure LinearCode (F : Type*) [Field F] [Fintype F] (n : ℕ)
  extends Submodule F (Fin n → F)

namespace LinearCode

/-- To view a Linear Code as a code -/
def toCode (C : LinearCode F n) : Code F n := (C.toSubmodule : Set (Fin n → F))

/-- Coercion so we can treat Linear Code as a code (essentially applies toCode) -/
instance : Coe (LinearCode F n) (Code F n) := ⟨toCode⟩

/-- Simple proof that a linear code is a code -/
@[simp] lemma mem_toCode {C : LinearCode F n} {c : Fin n → F} :
    c ∈ C.toCode ↔ c ∈ C.toSubmodule := Iff.rfl

/-- Inherit dim from code -/
noncomputable def dim (C : LinearCode F n) : ℝ := C.toCode.dim

/-- Inherit rate from code -/
noncomputable def rate (C : LinearCode F n) : ℝ := C.toCode.rate

/-- If C is an [n,k]_q linear code then there is a matrix G ∈ 𝔽^{k × n}_q
of rank k satisfying C = {x · G ∣ x ∈ 𝔽^k_q} -/
def GeneratorMatrix {k : ℕ} (G : Matrix (Fin k) (Fin n) F) : LinearCode F n :=
  ⟨LinearMap.range (vecMulLinear G)⟩

/-- If C is an [n,k]_q linear code then there is a matrix H ∈ 𝔽^{(n-k) × n}_q
of rank n-k satisfying C = {y ∈ 𝔽_q^n ∣ H · y^⊺ = 0} -/
def ParityCheckMatrix {m : ℕ} (H : Matrix (Fin m) (Fin n) F) : LinearCode F n :=
  ⟨LinearMap.ker (mulVecLin H)⟩

/-- If C is an [n,k]_q linear code then there is a matrix G ∈ 𝔽^{k × n}_q
of rank k satisfying C = {x · G ∣ x ∈ 𝔽^k_q} -/
lemma SubspaceImpliesGenerator {C : LinearCode F n} :
    ∃ k : ℕ, (k ≤ n) ∧ (dim C = k) ∧
    ∃ G : Matrix (Fin k) (Fin n) F, (GeneratorMatrix G = C) ∧ (Matrix.rank G = k) := by sorry

/-- If G ∈ 𝔽^{k × n}_q is a matrix of rank k satisfying C = {x · G ∣ x ∈ 𝔽^k_q}
then C is an [n,k]_q linear code -/
lemma GeneratorImpliesSubspace {G : Matrix (Fin k) (Fin n) F} :
    Matrix.rank G = k → ∃ C : LinearCode F n, (GeneratorMatrix G = C) ∧ (dim C = k) := by sorry

/-- If C is an [n,k]_q linear code then there is a matrix H ∈ 𝔽^{(n-k) × n}_q
of rank n-k satisfying C = {y ∈ 𝔽_q^n ∣ H · y^⊺ = 0} -/
lemma subspaceImpliesParityCheck {C : LinearCode F n} :
    ∃ m : ℕ, (m ≤ n) ∧ (dim C + m = n) ∧
    ∃ H : Matrix (Fin m) (Fin n) F, (ParityCheckMatrix H = C) ∧ (Matrix.rank H = m) := by sorry

/-- If H ∈ 𝔽^{(n-k) × n}_q is a matrix of rank n-k satisfying
C = {y ∈ 𝔽_q^n ∣ H · y^⊺ = 0} then C is an [n,k]_q linear code-/
lemma ParityCheckImpliesSubspace {H : Matrix (Fin m) (Fin n) F} :
    Matrix.rank H = m → ∃ C : LinearCode F n, (ParityCheckMatrix H = C) ∧ (dim C = n-m) := by sorry

end LinearCode

end

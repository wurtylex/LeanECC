/-
Copyright (c) 2026 wurtylex (Anthony Chang). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Chai, Erin Jaen, wurtylex (Anthony Chang) 
-/

module

public import Mathlib.LinearAlgebra.Matrix.Rank
/-!
## Linear Codes via Generator and Parity-Check Matrices

A **linear code** of blocklength `n` over a field `F` is a subspace of `F^n`.
Two standard matrix presentations exist:

* **Generator matrix** `G : F^{k×n}` — the code is the row space of `G`,
  i.e., the image of `v ↦ v ᵥ* G`.
* **Parity-check matrix** `H : F^{m×n}` — the code is the right null space of `H`,
  i.e., the kernel of `v ↦ H *ᵥ v`.
-/

@[expose] public section

namespace LinearCode

open Matrix

variable {F : Type*} [Field F] {n : ℕ}

/-- The linear code with generator matrix `G : F^{k×n}` is the image of the
    row-multiplication linear map `v ↦ v ᵥ* G`.  A codeword is any `F`-linear
    combination of the rows of `G`. -/
def GeneratorMatrix {k : ℕ} (G : Matrix (Fin k) (Fin n) F) :
    Subspace F (Fin n → F) :=
  LinearMap.range (vecMulLinear G)

/-- Membership in the generator-matrix code: `c` is a codeword iff it is
    `v ᵥ* G` for some coefficient vector `v`. -/
@[simp]
theorem mem_GeneratorMatrix {k : ℕ} {G : Matrix (Fin k) (Fin n) F}
    {c : Fin n → F} :
    c ∈ GeneratorMatrix G ↔ ∃ v : Fin k → F, v ᵥ* G = c := by
  simp only [GeneratorMatrix, LinearMap.mem_range, vecMulLinear_apply]

/-- The linear code with parity-check matrix `H : F^{m×n}` is the kernel of
    the matrix-vector linear map `v ↦ H *ᵥ v`.  A codeword must satisfy
    every parity-check equation imposed by the rows of `H`. -/
def ParityCheckMatrix {m : ℕ} (H : Matrix (Fin m) (Fin n) F) :
    Subspace F (Fin n → F) :=
  LinearMap.ker (mulVecLin H)

/-- Membership in the parity-check code: `c` is a codeword iff `H *ᵥ c = 0`. -/
@[simp]
theorem mem_ParityCheckMatrix {m : ℕ} {H : Matrix (Fin m) (Fin n) F}
    {c : Fin n → F} :
    c ∈ ParityCheckMatrix H ↔ H *ᵥ c = 0 := by
  simp only [ParityCheckMatrix, LinearMap.mem_ker, mulVecLin_apply]

end LinearCode

end

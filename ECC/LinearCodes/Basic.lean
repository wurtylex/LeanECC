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

/- Note that this is proper definition
finite field can only contain a number of elements equal to a prime power -/

structure LinearCode (F : Type*) [Field F] [Fintype F] (n : ℕ)
  extends Submodule F (Fin n → F)

namespace LinearCode

/-- To view a Linear Code as a code -/
def toCode (C : LinearCode F n) : Code F n := (C.toSubmodule : Set (Fin n → F))

instance : Membership (Fin n → F) (LinearCode F n) :=
  ⟨fun C c => c ∈ C.toSubmodule⟩

/-- The linear code with generator matrix `G : F^{k×n}` is the image of the
    row-multiplication linear map `v ↦ v ᵥ* G`.  A codeword is any `F`-linear
    combination of the rows of `G`. -/
def GeneratorMatrix {k : ℕ} (G : Matrix (Fin k) (Fin n) F) : LinearCode F n :=
  ⟨LinearMap.range (vecMulLinear G)⟩

/-- The linear code with parity-check matrix `H : F^{m×n}` is the kernel of
    the matrix-vector linear map `v ↦ H *ᵥ v`.  A codeword must satisfy
    every parity-check equation imposed by the rows of `H`. -/
def ParityCheckMatrix {m : ℕ} (H : Matrix (Fin m) (Fin n) F) : LinearCode F n :=
  ⟨LinearMap.ker (mulVecLin H)⟩

end LinearCode

end

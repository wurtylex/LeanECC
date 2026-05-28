import Mathlib.Data.Set.Basic

variable (α : Type _) (n : ℕ)

-- Code of blocklength n over α is a subset α^n
def Code : Tpe _ := Set (Fin n → α)

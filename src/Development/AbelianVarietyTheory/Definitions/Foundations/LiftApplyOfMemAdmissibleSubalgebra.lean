module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep

@[expose] public section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ

def admissibleLettersSubalgebra (R : Type) [CommRing R] (N l : ℕ) : Subalgebra R (FreeAlgebra R Letter) :=
  Algebra.adjoin R (FreeAlgebra.ι R '' {T | admitted N l T})

def SSPotB (N l w : ℕ) (lam : Letter → ℂ) : Prop :=
  ∃ P ∈ admissibleLettersSubalgebra ℂ N l, FreeAlgebra.lift ℂ lam P = 1 ∧ ∀ F ∈ Pot ℂ w (Gam N l), ∀ T : Letter, admitted N l T →
    (opL ℂ N l T - lam T • (1 : Module.End ℂ (ℂ → MvPolynomial (Fin 2) ℂ)))
      (FreeAlgebra.lift ℂ (opL ℂ N l) P F) ∈ Triv ℂ w (Gam N l)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Tower.SSBB (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] (lam : Letter → E) :
    Prop :=
  ∃ P ∈ admissibleLettersSubalgebra E N l, FreeAlgebra.lift E lam P = 1 ∧ ∀ x ∈ X.VB N l w E, ∀ T : Letter, admitted N l T →
    (X.opV N l E T - lam T • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l))) (FreeAlgebra.lift E (X.opV N l E) P x) = 0

theorem iota_mem_admissibleSubalgebra (R : Type) [CommRing R] {N l : ℕ} {T : Letter} (hT : admitted N l T) :
    FreeAlgebra.ι R T ∈ admissibleLettersSubalgebra R N l :=
  Algebra.subset_adjoin ⟨T, hT, rfl⟩

end GlobalTheory.KZ

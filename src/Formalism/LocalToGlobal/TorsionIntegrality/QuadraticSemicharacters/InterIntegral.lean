module

public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactVersion

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

def IntAt (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (lg ph : PowerSeries ℂ_[l]) {n : Type} [Fintype n] [DecidableEq n]
    (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (B' : Matrix n n ℂ_[l]) (θ : (n → ℂ) → ℂ) : Prop :=
  ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ Λ →
    Integral (mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[l]) *
      thetaU (ι : ℂ →+* ℂ_[l]) lg B' (opU (matH h) t θ))

end Formalism.L2.Th1.H

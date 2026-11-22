module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

abbrev ProjectiveLineBundle.Diag {D : ℕ} (S : ProjectiveLineBundle D) : Ideal (MRing S.WIdx) :=
  T.wwIdeal S.x S.δ S.e S.φ (S.a 0) (S.a 0)

section Statements

def ZeroSetNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (s : MRing ι)
    (a : K → ℕ) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g₁ g₂ : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsMultiHomog s a → s ∉ P →
    (∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) s) ≠ 0 → g₁ z = g₂ z) →
    ptsIntegral P φ g₁ = ptsIntegral P φ g₂

end Statements

section Inhabit

end Inhabit

end

end GroundTheory.Heights₂.Heights.Inter

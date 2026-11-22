module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralCoeffsOfGeometricFixedQExpansion
public import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow

@[expose] public section

open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_coeffs_of_geometric_fixed_qExpansion : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (N : ℕ) (c : ℕ → Ω), (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) →
    IsInt (p := p) (∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) →
      ∀ j < p ^ N, IsInt (p := p) (c j) := by
  first | exact @GlobalTheory.K5.OrthDecomp.orth | exact GlobalTheory.K5.OrthDecomp.orth | (intros; apply GlobalTheory.K5.OrthDecomp.orth <;> assumption)

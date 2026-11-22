module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerParameterPowersOrthogonalGeometricInvariant

@[expose] public section

open GlobalTheory.K5

namespace GlobalTheory.K5.OrthDecomp

theorem orth : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (N : ℕ) (c : ℕ → Ω), (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) →
      IsInt (p := p) (∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) →
        ∀ j < p ^ N, IsInt (p := p) (c j) :=
  GlobalTheory.K5.Orth.orth

end GlobalTheory.K5.OrthDecomp

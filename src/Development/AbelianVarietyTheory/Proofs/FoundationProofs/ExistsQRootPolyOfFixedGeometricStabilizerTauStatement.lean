module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsQRootPolyOfFixedGeometricStabilizerTau
public import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow

@[expose] public section

open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_qRoot_poly_of_fixed_geometric_stabilizer_tau : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo (p := p) Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (z : Ω), (∀ g ∈ Ggeo (p := p) Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g z = z) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) ∧ z = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j :=
  GlobalTheory.K5.Span.span

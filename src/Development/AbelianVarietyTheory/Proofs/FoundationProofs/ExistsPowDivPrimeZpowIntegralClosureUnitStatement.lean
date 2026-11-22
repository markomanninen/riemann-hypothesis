module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowDivPrimeZpowIntegralClosureUnit
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

@[expose] public section

open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_div_prime_zpow_integralClosure_unit : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ x : Ω, x ≠ 0 → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ IsInt (p := p) (x ^ b / (p : Ω) ^ a) ∧
    IsInt (p := p) ((p : Ω) ^ a / x ^ b) := by
  intro p _ Ω _ _ hΩ x hx
  obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
  have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
    rw [hmax]
    exact o0_isAdicComplete_span_p p
  have : FaithfulSMul (O0 p) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hΩ.inj
  let _ : Algebra (FractionRing (O0 p)) Ω := FractionRing.liftAlgebra (O0 p) Ω
  have : IsScalarTower (O0 p) (FractionRing (O0 p)) Ω :=
    FractionRing.isScalarTower_liftAlgebra (O0 p) Ω
  have : Algebra.IsAlgebraic (O0 p) Ω := hΩ.alg
  have : Algebra.IsAlgebraic (FractionRing (O0 p)) Ω :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) (FractionRing (O0 p)))
  have hIntegral := exists_pow_div_zpow_isIntegral (O0 p) (FractionRing (O0 p)) Ω (p : O0 p)
    hirr x hx
  simpa only [IsInt, map_natCast] using hIntegral

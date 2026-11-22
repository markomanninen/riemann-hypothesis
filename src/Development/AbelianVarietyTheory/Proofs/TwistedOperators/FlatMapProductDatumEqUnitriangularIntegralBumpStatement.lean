module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatMapProductDatumEqUnitriangularIntegralBump
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionMixedCoordinateBumpMulCoreStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTargetBumpMulCoreThetaExistsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionDeterminedByMixedCoordinatesStatement

namespace I195MixedCoordinates_22e9c63b07d64d8cd1eca31b

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_22e9c63b07d64d8cd1eca31b

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMap_productDatum_eq_unitriangularIntegral_bump : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (β₁ : Mx D W.rank ρ → ℝ) (β₂ : Mx D V₀.rank σ → ℂ) (g : WO V₀ W₀ → ℂ) (g' : WO V₀ W → ℂ) (Φ : WO V W → ℂ), g ≠ 0 → β₂ y ≠ 0 → (∀ x', (_root_.I195MixedCoordinates_22e9c63b07d64d8cd1eca31b.source dV) W ψ s.vS.μ s.vS.𝓕 Φ x' = (β₁ x' : ℂ) • g') → (∀ y', (_root_.I195MixedCoordinates_22e9c63b07d64d8cd1eca31b.target dW) V₀ ψ s.vT.μ s.vT.𝓕 g' y' = β₂ y' • g) → Continuous β₁ → β₁ x = 1 → (∀ z, 0 ≤ β₁ z) → (∀ u : UX D ρ, β₁ (x ⬝ u.1.1) ≠ 0 → 0 < (star (psiUni ψ u.1)).re) → HasCompactSupport (fun u : UX D ρ => β₁ (x ⬝ u.1.1)) → flatS dV dW s x y Φ ≠ 0 := by
  first | exact @GlobalTheory.FlatProdValue.flatS_ne_zero | exact GlobalTheory.FlatProdValue.flatS_ne_zero | (intros; apply GlobalTheory.FlatProdValue.flatS_ne_zero <;> assumption)

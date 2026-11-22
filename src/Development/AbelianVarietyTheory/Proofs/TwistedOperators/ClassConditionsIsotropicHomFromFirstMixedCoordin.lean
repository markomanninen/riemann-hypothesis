module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionMixedCoordinateBumpMulCoreStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTargetBumpMulCoreThetaExistsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionDeterminedByMixedCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum

namespace I195MixedCoordinates_acb50ed7a993b068b784d65f

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

end I195MixedCoordinates_acb50ed7a993b068b784d65f

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem GlobalTheory.ClassFromMixed.main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ), p.Is dV dW x ψ → ∀ (β₁ : Mx D W.rank ρ → ℂ) (g' : WO V₀ W → ℂ) (Φ : WO V W → ℂ), IsThetaFunO ψ V W Φ → (∀ x', (_root_.I195MixedCoordinates_acb50ed7a993b068b784d65f.source dV) W ψ vS.μ vS.𝓕 Φ x' = β₁ x' • g') → (∀ a ∈ p.A₁, ∀ z, β₁ (z + a) = β₁ z) → (∀ z, β₁ z ≠ 0 → ∃ r : Mx D W.rank ρ, r.map (finPart D) = 0 ∧ z - (x + r) ∈ p.A₁) → (∀ a ∈ p.A₁, heisO ψ V W (dV.extX W a) Φ = Φ) ∧ ∀ a ∈ p.A₂, heisO ψ V W (dV.extY W a) Φ = ψ (symplO V W (dV.extX W x) (dV.extY W a)) • Φ := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW vS p x hp β₁ g' Φ hΦ hmix hper hsupp
  obtain ⟨hX, hY, -⟩ := GlobalTheory.HeisMixSource.heis_mixS D ψ hψ V V₀ W ρ dV vS Φ hΦ
  change ∀ x', I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 Φ x' = β₁ x' • g' at hmix
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · refine (GlobalTheory.T.thetaFunction_determined_by_mixedCoordinates D ψ hψ V W _ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hΦ _) hΦ).1 V₀ ρ dV vS
      fun x' => ?_
    change I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 (heisO ψ V W (dV.extX W a) Φ) x' = I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 Φ x'
    rw [hX, hmix, hmix, hper a ha]
  · refine (GlobalTheory.T.thetaFunction_determined_by_mixedCoordinates D ψ hψ V W _ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hΦ _)
      (GlobalTheory.WeilVacMove.isTheta_smul _ hΦ)).1 V₀ ρ dV vS fun x' => ?_
    change I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 (heisO ψ V W (dV.extY W a) Φ) x' = I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 (ψ (symplO V W (dV.extX W x) (dV.extY W a)) • Φ) x'
    have hsmul := GlobalTheory.HandHom.mixS_smul dV W ψ vS.μ vS.𝓕 (ψ (symplO V W (dV.extX W x) (dV.extY W a))) Φ x'
    change I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 (ψ (symplO V W (dV.extX W x) (dV.extY W a)) • Φ) x' = ψ (symplO V W (dV.extX W x) (dV.extY W a)) • I195MixedCoordinates_5a743adb4eaabe3d936622f8.source dV W ψ vS.μ vS.𝓕 Φ x' at hsmul
    rw [hY, hsmul, hmix]
    by_cases hb : β₁ x' = 0
    · rw [hb, zero_smul, smul_zero, smul_zero]
    · obtain ⟨r, hr, hx'⟩ := hsupp x' hb
      have hfinA : MxAt (fun _ => True) a := hp.a₂.fin a ha
      have hYa : (dV.extY W a).map (infPart D) = 0 := by
        rw [HypDec.extY_apply, Matrix.map_mul]
        have : a.map (infPart D) = 0 := Matrix.ext fun i j => GlobalTheory.FinPlLoc.infPart_of_idAt (hfinA i j)
        rw [this, Matrix.zero_mul]
      have hXr : (dV.extX W r).map (finPart D) = 0 := by
        rw [HypDec.extX_apply, Matrix.map_mul, hr, Matrix.zero_mul]
      have h1 : ψ (symplO V W (dV.extX W (x' - (x + r))) (dV.extY W a)) = 1 :=
        (hp.dualA _ (hp.a₁.fin _ hx')).1 hx' a ha
      have hsplit : x' = x + r + (x' - (x + r)) := by abel
      have key : ψ (symplO V W (dV.extX W x') (dV.extY W a)) = ψ (symplO V W (dV.extX W x) (dV.extY W a)) := by
        rw [hsplit, map_add (f := _), map_add (f := _), GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_left,
          GlobalTheory.SplitScalar.symplO_real_fin V W hXr hYa, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h1,
          AddChar.map_zero_eq_one, mul_one, mul_one]
      rw [key]

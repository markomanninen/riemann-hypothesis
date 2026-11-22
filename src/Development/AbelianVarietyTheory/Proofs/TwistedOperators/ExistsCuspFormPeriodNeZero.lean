module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesCoefficientsCuspidalIffOneSided
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentPeriodAdelicClausesOfRealStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormCuspFormLeOfShortLineStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesIdentityTermDominatesStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsQuotHeightMulExpInfLe
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesIsAutomorphicStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesSmoothModerateGrowthDerivStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldTsumAlongSubgroupStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsCuspFunOnePlane
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralUnfoldingLeOfTranslateCoverStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesPartialSumsBoundedCompactStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurableLevelIndicatorCoefficientTestFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralHaarEqZeroOfFibreIntegralsEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClosedParabolicSubgroups
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkMapCuspFormsExtendsToSmoothVectors
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientDecayKFiniteSecondVectorStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRowGridBottomSelfDualLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentPeriodValueLipschitzRealOneParameterStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TprodEqZeroOfKFinOff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultRealElt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SurjectiveTopMap
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesMoveRealPointStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBoundMultiplicityValueExceedsHalfStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsContAutRTrans

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepPer.PerNe

theorem multT_apply_mul_lev {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S}
    {J : Set (GA D V)} {χ : GA D V → ℂ} {F : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hF : F ∈ MultT θ M J χ) (v : SmT M) :
    ∀ k ∈ J, ∀ g, F v (g * k) = χ k * F v g := by
  obtain ⟨T, hT, rfl⟩ := hF
  induction hT using Submodule.span_induction generalizing v with
  | mem T hT =>
    induction v using PiTensorProduct.induction_on with
    | smul_tprod r w =>
      intro k hk g
      simp only [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod, Pi.smul_apply, smul_eq_mul]
      rw [hT.lev w k hk g]; ring
    | add x y hx hy =>
      intro k hk g
      simp only [map_add (f := _), Pi.add_apply]
      rw [hx k hk g, hy k hk g]; ring
  | zero => intro k hk g; simp
  | add T₁ T₂ _ _ h₁ h₂ =>
    intro k hk g
    simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply]
    rw [h₁ v k hk g, h₂ v k hk g]; ring
  | smul c T _ h =>
    intro k hk g
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [h v k hk g]; ring

theorem apply_tprod_eq {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    {X : Type} [AddCommGroup X] [Module ℂ X] (y : (⨂[ℂ] i, E i) →ₗ[ℂ] X) (a : ∀ i, E i) :
    y (PiTensorProduct.tprod ℂ a) = PiTensorProduct.lift.symm y a := by
  conv_lhs => rw [← PiTensorProduct.lift.apply_symm_apply y]
  exact PiTensorProduct.lift.tprod _

end GlobalTheory.SepPer.PerNe

namespace GlobalTheory.SepPer

end GlobalTheory.SepPer

end

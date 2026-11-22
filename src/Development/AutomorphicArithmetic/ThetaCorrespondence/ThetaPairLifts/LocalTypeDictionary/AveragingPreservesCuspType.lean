module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobZeroNeTop
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKModuleMapCuspFormsExtendsMultiplicitySpace
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmoothVectorsDiscreteSeriesModelIffStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFinAtZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSmoothAutomorphicFunctionCompactFamilyAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStabEmpty
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeriesAverageOtherPlaceType
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KFiniteCuspFormAverageApprox
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.AverageIsTypeAtSamePlaceTwist
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.AverageIsTypeAtOtherPlaceTwist

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
namespace GlobalTheory.AvgCuspType
theorem cusp_average_isCuspOfType : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N ψ → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  intro D θ hθ hp N ψ hψ τ e he
  have hc : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
  refine ⟨?_, _root_.GlobalTheory.KFinCuspApprox.isCuspForm_kFinite_average θ hθ hp N τ e hc ψ hψ.1 hψ.2.1, fun τ' => ?_⟩
  · exact GlobalTheory.RealAverage.isAutFunSm_average D θ hθ N.V τ (Formalism.REAL.KG (N.M.ε τ)) (Formalism.REAL.muK (N.M.ε τ)) _
      GlobalTheory.SeriesToClosure.continuous_conjK
      (fun k => GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ) (N.M.fr_gram τ) k) e hc ψ hψ.1
  · by_cases h : τ' = τ
    · subst h
      exact _root_.GlobalTheory.T.average_isTypeAt_same_place_twist D θ hθ hp N τ' ψ hψ.1 (hψ.2.2 τ') e he
    · exact _root_.GlobalTheory.T.average_isTypeAt_other_place_twist D θ hθ hp N τ τ' h ψ hψ.1 (hψ.2.2 τ') e he
end GlobalTheory.AvgCuspType
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.averaging_preserves_cusp_type : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N ψ → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  first | exact @_root_.GlobalTheory.AvgCuspType.cusp_average_isCuspOfType | exact _root_.GlobalTheory.AvgCuspType.cusp_average_isCuspOfType | (intros; apply _root_.GlobalTheory.AvgCuspType.cusp_average_isCuspOfType <;> assumption)
end

module

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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSmoothAutomorphicFunctionCompactFamilyAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStabEmpty
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeriesAverageOtherPlaceType
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AveragedAutomorphicFunctionKFiniteStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AveragePreservesKFinitenessStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DecompAtZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasCtpId
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkGeneratedCuspFormsOfType
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormsOfVertexTypeZeroMemAndSmulMemStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacePointCommuteOfNePlace
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AveragePreservesKFiniteness
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgTypeOtherPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimStableSpaceMaxCompactAverages
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteReproducingFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteDecompositionAssembleRealPlacesStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section
namespace GlobalTheory.CuspKFinDecomp

theorem avg_lev : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ) (U : Subgroup (GA D N.V)), (∀ k ∈ U, k ∈ GfC N.V → ∀ g, ψ (g * k) = ψ g) → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), ∀ k ∈ U, k ∈ GfC N.V → ∀ g, GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ (g * k) = GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ g := by
  intro D θ hθ N ψ U hψ τ e k hk hkf g
  unfold GlobalTheory.SeriesToClosure.avg
  congr 1
  funext k'
  rw [mul_assoc, ← GlobalTheory.PointAtPlaceHom.comm_of_mem N.V (GlobalTheory.PointAtPlaceHom.atTau_mem N.V τ _) hkf, ← mul_assoc,
    hψ k hk hkf]

end GlobalTheory.CuspKFinDecomp
end

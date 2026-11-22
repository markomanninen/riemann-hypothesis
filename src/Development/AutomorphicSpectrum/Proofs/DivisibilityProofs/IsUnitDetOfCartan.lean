module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.GlobalDatumRegularityOfTypesCompatibility
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.WeilRepresentationSplittingsDiffer
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumTensorProduct
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.RationalUnitsHaarCharacterOneStatement
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.SplitQuadraticAlgebraOrder
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FiniteNonunitMatrix
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.RemovableLogGrowthSingularityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianDarbouxSplitProductStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmAlgebraSplitInvolution

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.IndefR.Mult IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.CompanionTheory.Ar.RT
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix
open scoped NNReal

namespace GlobalTheory.CompanionTheory.Ar.RT

theorem det_ne_zero_of_cartan {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan M θ) : M.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hx : star v ≠ 0 := fun e => hv (by simpa using congrArg star e)
  have := h.2.2 (star v) hx
  rw [star_star, hMv, dotProduct_zero] at this
  simp at this


open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem isUnit_det_of_cartan {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (τ : E →+* ℂ) (s : ℂ) (θ : Matrix (Fin n) (Fin n) ℂ)
    (h : IsCartan (s • J.map τ) θ) : IsUnit J.det := by
  refine isUnit_iff_ne_zero.mpr fun h0 => det_ne_zero_of_cartan h ?_
  rw [Matrix.det_smul, show (J.map τ).det = τ J.det from (RingHom.map_det τ J).symm, h0, map_zero, mul_zero]


end GlobalTheory.CompanionTheory.Ar.RT

end

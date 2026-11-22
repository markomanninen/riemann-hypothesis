module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleMonomialSupportFinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleRationalCoefficients
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleOpenSubgroupField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleFiniteDoubleCosets
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleDualAlgebraicityFiniteData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightedAverageHaar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFourierDegreeBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelAlgebraicExpansion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRepSuppSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAlgebraicStdCharHalfSymplecticRealPartZeroStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumValueAlgebraicCongruence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLocalSupportIdempotent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGfCOfSuppAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingNegativeVacuumDefiniteBottom
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryInductionOnSplitPlaceSupportStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsOnVacuumByAlgebraicScalarStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicFixedDegree
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumFinitePairVacuumAlgebraicCombinationStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFourierIndexRationalPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierIndexRationalPairValue
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightedAverageHaarLifted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanUnitaryWeights
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AverageDetCharMonomialEqSumProdMinorsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicLiftedKernel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSumPairCoordinateAlgebraic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RowEx.BotField

theorem field_of_gens {T Hh κ : Type} [Finite T] (v : T → Hh → κ → ℂ) (good : Set Hh)
    (hab : ∃ (H : Finset Hh) (K : Finset κ) (M₀ : IntermediateField ℚ ℂ), FiniteDimensional ℚ M₀ ∧ (∀ h ∈ H, h ∈ good) ∧
      ∀ t, ∀ h ∈ good, ∀ k, ∃ c : Hh → κ → ℂ, (∀ a b, c a b ∈ M₀) ∧ v t h k = ∑ h' ∈ H, ∑ k' ∈ K, c h' k' * v t h' k')
    (hc : ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ good, ∀ k, IsAlgebraic ℚ (v t h k / Ω)) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ good, ∀ k, v t h k / Ω ∈ M := by
  obtain ⟨H, K, M₀, hM₀, hH, hv⟩ := hab
  obtain ⟨Ω, hΩ, halg⟩ := hc
  let S : Set ℂ := Set.range fun x : T × H × K => v x.1 x.2.1 x.2.2 / Ω
  haveI : Finite S := Set.finite_range _ |>.to_subtype
  have hS : ∀ z ∈ S, IsIntegral ℚ z := by
    rintro _ ⟨⟨t, h, k⟩, rfl⟩
    exact (halg t h (hH h h.2) k).isIntegral
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) := IntermediateField.finiteDimensional_adjoin hS
  refine ⟨M₀ ⊔ IntermediateField.adjoin ℚ S, inferInstance, Ω, hΩ, fun t h hh k => ?_⟩
  obtain ⟨c, hc, e⟩ := hv t h hh k
  rw [e, Finset.sum_div]
  refine sum_mem fun h' hh' => ?_
  rw [Finset.sum_div]
  refine sum_mem fun k' hk' => ?_
  rw [mul_div_assoc]
  refine mul_mem ((le_sup_left : M₀ ≤ _) (hc h' k')) ((le_sup_right : IntermediateField.adjoin ℚ S ≤ _) ?_)
  exact IntermediateField.subset_adjoin ℚ S ⟨⟨t, ⟨h', hh'⟩, ⟨k', hk'⟩⟩, rfl⟩

theorem sumsIn_mono {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {A A' WW : HSp D}
    {X : Tri T A A' WW} {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} (h : SumsIn W σ X)
    (hσ : Set.range σ ⊆ Set.range σ') : SumsIn W σ' X := by
  obtain ⟨Ω, Ω', h0, h0', H⟩ := h
  exact ⟨Ω, Ω', h0, h0', fun t g hg => ⟨fun k hk => hσ ((H t g hg).1 k hk), fun k hk => hσ ((H t g hg).2 k hk)⟩⟩

end GlobalTheory.RowEx.BotField

end

module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightedAverageHaarLifted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanUnitaryWeights
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AverageDetCharMonomialEqSumProdMinorsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicLiftedKernel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSumPairCoordinateAlgebraic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomClassSumEqFormula
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.NormSumCoefficientsIsAlgebraic

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
namespace GlobalTheory.BotAlgI'
theorem twistedClassSums_isAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, IsAlgebraic ℚ (X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h / Ω) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX
  obtain ⟨Ω, hΩ, H⟩ := _root_.GlobalTheory.T.bottomClassSum_eq_formula hP hI hL hX
  refine ⟨Ω, hΩ, fun t h hh k => ?_⟩
  obtain ⟨n, c, z, hc, hz, he⟩ := H t h hh k
  rw [he, mul_div_cancel_left₀ _ hΩ]
  have hz' : ∀ l, IsAlgebraic ℚ (z l) := fun l => by
    obtain ⟨δ, t0, Q, P, h', U, e⟩ := hz l
    rw [e]; exact _root_.GlobalTheory.T.normSum_coefficients_isAlgebraic hP hI D δ t0 Q P h' U
  have : ∀ l, (c l * z l) ∈ algebraicClosure ℚ ℂ := fun l =>
    mul_mem (mem_algebraicClosure_iff.2 (hc l)) (mem_algebraicClosure_iff.2 (hz' l))
  exact mem_algebraicClosure_iff.1 (sum_mem fun l _ => this l)
end GlobalTheory.BotAlgI'
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_twistedClassSums_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, IsAlgebraic ℚ (X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h / Ω) := by
  first | exact @_root_.GlobalTheory.BotAlgI'.twistedClassSums_isAlgebraic | exact _root_.GlobalTheory.BotAlgI'.twistedClassSums_isAlgebraic | (intros; apply _root_.GlobalTheory.BotAlgI'.twistedClassSums_isAlgebraic <;> assumption)
end

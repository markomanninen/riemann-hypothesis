module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedCoordinateSupportIntegralAtLevel
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable

namespace I195MixedCoordinates_f893ad7fd8680f4ca1164b63

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

end I195MixedCoordinates_f893ad7fd8680f4ca1164b63

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedCoordinate_support_integral_at_level : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (V X S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec V S₀ r) (μ' : Measure (Mx D X.rank r))
    (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' →
    ∀ (K₀ : Set (WO V X)), K₀ ∈ nhds (0 : WO V X) → IsCompact K₀ →
    ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, 0 < n → ∀ Ψ : WO V X → ℂ, IsThetaFunO ψ V X Ψ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ V X (n • u) Ψ = Ψ) →
      ∀ (ξ : Matrix (Fin X.rank) (Fin r) D.host.E) (x : Mx D X.rank r),
        x.map (finPart D) = (ξ.map (incA D) : Mx D X.rank r).map (finPart D) → (_root_.I195MixedCoordinates_f893ad7fd8680f4ca1164b63.source d) X ψ μ' 𝓕' Ψ x 0 ≠ 0 →
        ∀ i j, IsIntegral ℤ (((M * n : ℕ) : D.host.E) * ξ i j) := by
  first | exact @GlobalTheory.MixSupport.mixS_support_integral | exact GlobalTheory.MixSupport.mixS_support_integral | (intros; apply GlobalTheory.MixSupport.mixS_support_integral <;> assumption)

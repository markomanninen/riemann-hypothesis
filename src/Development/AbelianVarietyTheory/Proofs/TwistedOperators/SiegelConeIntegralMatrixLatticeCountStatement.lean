module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SiegelConeIntegralMatrixLatticeCount
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable

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
theorem _root_.GlobalTheory.T.siegelCone_integral_matrix_lattice_count : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (m r : ℕ) (c : ℝ), 0 < c →
    ∃ (N A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ L : ℕ, 0 < L → ∀ t ∈ GlobalTheory.SiegelSet.cone r c,
      ∑' ξ : Matrix (Fin m) (Fin r) D.host.E,
        {ξ : Matrix (Fin m) (Fin r) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator
          (fun ξ => ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j,
            ‖(compAt θ τ (ξ.map (incA D) : Mx D m r) * diagonal (fun k => (t k : ℂ))) i j‖) ^ N)⁻¹) ξ ≤
        ENNReal.ofReal (C * (L : ℝ) ^ A) := by
  first | exact @GlobalTheory.LatCount.lattice_count | exact GlobalTheory.LatCount.lattice_count | (intros; apply GlobalTheory.LatCount.lattice_count <;> assumption)

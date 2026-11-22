module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExpSecondKindCoordinates
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSubLeOfDerivIcc

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_second_kind_coordinates : ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n), (∀ i, b i ∈ lieSet ε) →
    LinearIndependent ℝ b → (∀ Z ∈ lieSet ε, ∃ c : Fin d → ℝ, Z = ∑ i, c i • b i) →
    ∀ c : Fin d → ℝ, ∃ τ : ℝ → (Fin d → ℝ), τ 0 = 0 ∧ HasDerivAt τ c 0 ∧
      ∀ᶠ t in nhds (0 : ℝ), NormedSpace.exp (t • ∑ i, c i • b i) =
        (List.ofFn fun i => NormedSpace.exp (τ t i • b i)).prod := by
  first | exact @GlobalTheory.SecondKindChart.exp_eq_expProd_near_zero | exact GlobalTheory.SecondKindChart.exp_eq_expProd_near_zero | (intros; apply GlobalTheory.SecondKindChart.exp_eq_expProd_near_zero <;> assumption)

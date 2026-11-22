module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivative
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
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_matrixRightInvariantDerivative : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ), φ ∈ GlobalTheory.KFourier.polyV ε d → ∀ X : Mx n, inK ε X → GlobalTheory.KFourier.rder ε [X] φ ∈ GlobalTheory.KFourier.polyV ε d ∧ ∀ k : KG ε, HasDerivAt (fun t : ℝ => φ (k * expK ε X t)) (GlobalTheory.KFourier.rder ε [X] φ k) 0 := by
  first | exact @GlobalTheory.KFourier.rder_mem_and_hasDerivAt | exact GlobalTheory.KFourier.rder_mem_and_hasDerivAt | (intros; apply GlobalTheory.KFourier.rder_mem_and_hasDerivAt <;> assumption)

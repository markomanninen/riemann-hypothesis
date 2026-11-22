module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegralNormSqReproducingKernelLeFinrank
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
open GlobalTheory.KFourier MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_normSq_reproducingKernel_le_finrank : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), IsKer ε i e → ∫ k, ‖e k‖ ^ 2 ∂(muK ε) ≤ (Module.finrank ℂ (polyV ε i) : ℝ) := by
  first | exact @GlobalTheory.KFourier.integral_norm_sq_ker_le | exact GlobalTheory.KFourier.integral_norm_sq_ker_le | (intros; apply GlobalTheory.KFourier.integral_norm_sq_ker_le <;> assumption)

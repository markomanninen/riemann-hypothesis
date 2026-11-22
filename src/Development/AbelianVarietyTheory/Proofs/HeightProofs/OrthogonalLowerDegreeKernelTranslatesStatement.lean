module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthogonalLowerDegreeKernelTranslates
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
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivative

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_lowerDegree_kernel_translates : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (p κ : KG ε → ℂ), κ ∈ lowV ε i → (∀ q ∈ lowV ε i, ∫ k, q k * p k ∂(muK ε) = 0) → ∀ k : KG ε, ∫ x, star (p x) * κ (x⁻¹ * k) ∂(muK ε) = 0 := by
  first | exact @GlobalTheory.KFourier.orth_translate_lowV | exact GlobalTheory.KFourier.orth_translate_lowV | (intros; apply GlobalTheory.KFourier.orth_translate_lowV <;> assumption)

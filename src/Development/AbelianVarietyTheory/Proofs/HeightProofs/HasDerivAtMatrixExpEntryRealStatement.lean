module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasDerivAtMatrixExpEntryReal
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
theorem _root_.GlobalTheory.T.compactUnitaryAverage_mem_polyV : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), e ∈ GlobalTheory.KFourier.polyV ε i → ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → ∀ y ∈ UJset ε, GlobalTheory.KFourier.avgK ε e f y ∈ GlobalTheory.KFourier.polyV ε i := by
  first | exact @GlobalTheory.KFourier.avgK_mem | exact GlobalTheory.KFourier.avgK_mem | (intros; apply GlobalTheory.KFourier.avgK_mem <;> assumption)

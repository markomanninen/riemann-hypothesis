module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeasurableDerFamComp
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
theorem _root_.GlobalTheory.T.measurable_derFam_comp_continuous_of_mem_UJset : ∀ (n : ℕ) (ε : Fin n → Bool) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ), GlobalTheory.TypeSum.IsDerFam ε F →
    ContinuousOn (F []) (UJset ε) → ∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) →
    ∀ (T : Type) [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T] (φ : T → GlobalTheory.TypeSum.Mx n),
      Continuous φ → (∀ t, φ t ∈ UJset ε) → Measurable (fun t => F l (φ t)) := by
  first | exact @GlobalTheory.TypeSum.measurable_derFam_comp | exact GlobalTheory.TypeSum.measurable_derFam_comp | (intros; apply GlobalTheory.TypeSum.measurable_derFam_comp <;> assumption)

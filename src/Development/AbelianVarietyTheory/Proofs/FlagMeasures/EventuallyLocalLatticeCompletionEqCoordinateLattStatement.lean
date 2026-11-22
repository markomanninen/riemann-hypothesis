module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyLocalLatticeCompletionEqCoordinateLatt
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_localLatticeCompletion_eq_coordinateLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (b : Module.Basis (Fin d) F E) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, {X : Fin 1 → Fin n → Fv F v ⊗[F] E | X 0 ∈ GlobalTheory.AdelicU.latLoc F L v} = latV b v := by
  first
  | exact @GlobalTheory.AdelicU.Cofinite.eventually_latLoc_eq_latV
  | intro F E _ _ _ _ _ n d b L hL
    exact GlobalTheory.AdelicU.Cofinite.eventually_latLoc_eq_latV F E n d b L hL.toIsLattice

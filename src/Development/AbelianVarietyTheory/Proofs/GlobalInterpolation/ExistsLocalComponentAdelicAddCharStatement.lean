module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLocalComponentAdelicAddChar
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.DualExponentDensity
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ActionCoordinates
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDensityEuler
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeTensorUnfolding

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localComponent_adelicAddChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F), LocalAdditiveCharacterDual.IndexFinite F ψ v → ∃ χ : AddChar (Fv F v) ℂ, PlaceSplittingTypes.IsLocalChar F v χ ∧ ∀ t, χ t = psiV F ψ v t := by
  first | exact @GlobalTheory.LocalComponentChar.exists_localChar | exact GlobalTheory.LocalComponentChar.exists_localChar | (intros; apply GlobalTheory.LocalComponentChar.exists_localChar <;> assumption)

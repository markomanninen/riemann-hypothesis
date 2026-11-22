module

public import Mathlib
public import GroundTheory.AutomorphicForms.PartialDifferential.Sobolev

@[expose] public section

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

section Duality

variable {s : ℝ}

theorem bessel_ofSchwartz (φ : 𝓢(E, ℂ)) :
    SobolevSpace.bessel s (SobolevSpace.ofSchwartz s φ) =
      (SchwartzMap.fourierMultiplierCLM ℂ (weight s) φ).toLp 2 := by
  apply toTemperedDistribution_injective
  simp only
  rw [SobolevSpace.toDistribution_bessel, SobolevSpace.toDistribution_ofSchwartz,
    Lp.toTemperedDistribution_toLp_eq, besselPotential_eq_fourierMultiplierCLM,
    fourierMultiplierCLM_toTemperedDistributionCLM_eq (weight_hasTemperateGrowth _)]

end Duality

end

end GroundTheory.Automorphic.Sobolev

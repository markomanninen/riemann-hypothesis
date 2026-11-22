module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TruncatedDerivationLimit
public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

@[expose] public section

open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_derivation_limit : Factor → CutDer → CutLim := by
  first | exact @GlobalTheory.CompanionTheory.BesselCutLim.cutLim_of | exact GlobalTheory.CompanionTheory.BesselCutLim.cutLim_of | (intros; apply GlobalTheory.CompanionTheory.BesselCutLim.cutLim_of <;> assumption)

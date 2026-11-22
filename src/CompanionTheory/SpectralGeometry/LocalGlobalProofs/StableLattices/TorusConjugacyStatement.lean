module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugacy
public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

@[expose] public section

open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.TorusConjugacy : TorConj := by
  first | exact @GlobalTheory.CompanionTheory.BmuTorConj.torConj | exact GlobalTheory.CompanionTheory.BmuTorConj.torConj | (intros; apply GlobalTheory.CompanionTheory.BmuTorConj.torConj <;> assumption)

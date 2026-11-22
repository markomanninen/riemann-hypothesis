module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecomposition
public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

@[expose] public section

open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CartanDecomposition : CartanQ := by
  first | exact @GlobalTheory.CompanionTheory.BesselCartan.cartanQ | exact GlobalTheory.CompanionTheory.BesselCartan.cartanQ | (intros; apply GlobalTheory.CompanionTheory.BesselCartan.cartanQ <;> assumption)

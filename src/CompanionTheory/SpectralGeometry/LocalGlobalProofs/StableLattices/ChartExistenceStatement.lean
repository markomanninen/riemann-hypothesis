module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ChartExistence
public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

@[expose] public section

open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ChartExistence : ChartExists := by
  first | exact @GlobalTheory.CompanionTheory.ProdExChart.chartExists | exact GlobalTheory.CompanionTheory.ProdExChart.chartExists | (intros; apply GlobalTheory.CompanionTheory.ProdExChart.chartExists <;> assumption)

module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.LocalGeometry.Imports

@[expose] public section

namespace GlobalTheory

theorem geometricLemmaFiltration_unconditional : GlobalTheory.Published.GeometricLemmaFiltration :=
  CompanionTheory.Geo.geometricLemmaFiltration

end GlobalTheory

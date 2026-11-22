module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ComplexConjFrobeniusDepthContentBoundProof
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq

@[expose] public section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexConjFrobeniusDepthContentBound_proof : PhiCBd := by
  first | exact @GlobalTheory.GoodDepth.ConjPkg.phiCBd | exact GlobalTheory.GoodDepth.ConjPkg.phiCBd | (intros; apply GlobalTheory.GoodDepth.ConjPkg.phiCBd <;> assumption)

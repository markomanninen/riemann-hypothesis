module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.JacquetShalikaRigidity
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ResidualIrreducibilityFormsEquivalent
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport

@[expose] public section

namespace GlobalTheory.Fc.S0

structure Hypotheses2 : Prop extends Hypotheses1 where
  litN : GlobalTheory.Mem.LiteralAutomorphy.LitN
  toHypothesesX : GlobalTheory.NRows.HypothesesX
  nLink : GlobalTheory.NLink.Hypotheses₂
  depthZeroWild' : GlobalTheory.Published.DepthZeroWild
  depthZeroSupport' : GlobalTheory.Published.DepthZeroSupport

end GlobalTheory.Fc.S0

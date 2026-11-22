module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PositiveDefiniteUnitSphereMassProof
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positiveDefiniteUnitSphereMass_proof : GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.SphereMass := by
  first | exact @GlobalTheory.SphereMassProof.sphereMass | exact GlobalTheory.SphereMassProof.sphereMass | (intros; apply GlobalTheory.SphereMassProof.sphereMass <;> assumption)

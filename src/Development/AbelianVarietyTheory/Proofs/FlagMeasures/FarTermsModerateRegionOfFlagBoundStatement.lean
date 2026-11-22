module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FarTermsModerateRegionOfFlagBound
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FarTermSum
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FarTermsLatticeBound
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.farTermsModerateRegion_of_flagBound : GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Deep.FarBound → GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.FarModerate := by
  first | exact @GlobalTheory.Deep.farModerate_of_farBound | exact GlobalTheory.Deep.farModerate_of_farBound | (intros; apply GlobalTheory.Deep.farModerate_of_farBound <;> assumption)

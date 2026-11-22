module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedSumsFifthEstimate
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RamifiedSumsFifthBound

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_gap_bound : _root_.GlobalTheory.BigTop.Fun.RankGapBound' := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.rankGapBound_alt | exact _root_.GlobalTheory.BigTop.Fun.rankGapBound_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.rankGapBound_alt <;> assumption)
end

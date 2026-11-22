module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRootOfExp
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaleRootOfPrint
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvOfRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSeriesOfReciprocityHypotheses
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpAlgAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpAlgAltAlt

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expAlg_of_cusp_decay_and_reciprocity : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.ExpAlgAlt := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.expAlg_alt | exact _root_.GlobalTheory.BigOn.Exp.expAlg_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.expAlg_alt <;> assumption)
end

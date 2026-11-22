module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesRatOfSeriesRatS
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealizationEmbeddingCompatible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientLatticeSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedEmbeddingCompatibilityRows
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingScalarsIntegral
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwGe

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_lower_bound_of_prints : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.TwistLowerBound := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.twGe_alt | exact _root_.GlobalTheory.BigOn.Exp.twGe_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.twGe_alt <;> assumption)
end

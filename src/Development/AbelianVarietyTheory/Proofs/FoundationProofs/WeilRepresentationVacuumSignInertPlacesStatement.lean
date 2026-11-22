module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationVacuumSignInertPlaces
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_vacuum_sign_inert_places : ∀ D : D7, odd3 D := by
  first | exact @GlobalTheory.InertSign.vacuum_inert | exact GlobalTheory.InertSign.vacuum_inert | (intros; apply GlobalTheory.InertSign.vacuum_inert <;> assumption)

module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRatioStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_ratio_statement : ∀ D : D7, UnitaryVolumeMass.stMassRatio D := by
  first | exact @GlobalTheory.MassAtRecord.massRatio_at_record | exact GlobalTheory.MassAtRecord.massRatio_at_record | (intros; apply GlobalTheory.MassAtRecord.massRatio_at_record <;> assumption)

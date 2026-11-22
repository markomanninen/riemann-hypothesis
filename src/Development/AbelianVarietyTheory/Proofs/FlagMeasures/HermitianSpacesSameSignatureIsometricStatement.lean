module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianSpacesSameSignatureIsometric
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_spaces_same_signature_isometric : SameKindIsometric := by
  first | exact @GlobalTheory.FlagMeas.sameKindIsometric | exact GlobalTheory.FlagMeas.sameKindIsometric | (intros; apply GlobalTheory.FlagMeas.sameKindIsometric <;> assumption)

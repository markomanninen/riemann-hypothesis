module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowShareRequirementClosedFormProof
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.windowShareRequirementClosedForm_proof : DC.WClosed := by
  first | exact @GlobalTheory.EX.G4.wClosed | exact GlobalTheory.EX.G4.wClosed | (intros; apply GlobalTheory.EX.G4.wClosed <;> assumption)

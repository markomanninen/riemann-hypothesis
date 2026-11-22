module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSums
public import Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis

@[expose] public section

open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelsUsed_balancedValue_orbitSums : ThlEq ∧ LevelBound ∧ LemmaFe ∧ FInertReps := by
  first | exact @GlobalTheory.LevelsOrbits.main | exact GlobalTheory.LevelsOrbits.main | (intros; apply GlobalTheory.LevelsOrbits.main <;> assumption)

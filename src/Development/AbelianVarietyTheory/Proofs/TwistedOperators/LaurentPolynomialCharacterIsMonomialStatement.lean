module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LaurentPolynomialCharacterIsMonomial
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

@[expose] public section

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentPolynomial_character_isMonomial : GlobalTheory.RegSS.CharacterMonomial := by
  first | exact @GlobalTheory.RegSS.characterMonomial | exact GlobalTheory.RegSS.characterMonomial | (intros; apply GlobalTheory.RegSS.characterMonomial <;> assumption)

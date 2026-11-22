module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithInterProjectionFormulaOfHeightProjectionFor
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithInterProjectionFormula_of_heightProjectionFormula : GlobalTheory.Published.HeightProjection → GlobalTheory.Published.ArProj := by
  first | exact @GlobalTheory.Published.arProj_of_heightProjection | exact GlobalTheory.Published.arProj_of_heightProjection | (intros; apply GlobalTheory.Published.arProj_of_heightProjection <;> assumption)

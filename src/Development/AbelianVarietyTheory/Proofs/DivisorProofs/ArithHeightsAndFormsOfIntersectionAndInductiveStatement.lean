module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightsAndFormsOfIntersectionAndInductive
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHeightsAndForms_of_intersection_and_inductive : GlobalTheory.Published.ArFormExists → GlobalTheory.Published.ArMix → GlobalTheory.Published.ArExists := by
  first | exact @GlobalTheory.Published.arExists_of_form_of_mix | exact GlobalTheory.Published.arExists_of_form_of_mix | (intros; apply GlobalTheory.Published.arExists_of_form_of_mix <;> assumption)

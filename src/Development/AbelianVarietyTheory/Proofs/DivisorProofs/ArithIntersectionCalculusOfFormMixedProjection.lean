module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightsAndFormsOfIntersectionAndInductiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSelfInterConstantShiftOfTrivialWeightFormulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithInterChangeOfMetricOfMixedInductiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithInterProjectionFormulaOfHeightProjectionForStatement

@[expose] public section

namespace GlobalTheory.Published

theorem arCalc_of_form_mix_projection : ArFormExists → ArMix → HeightProjection → ArCalc := fun hF hM hP =>
  have hE : ArExists := GlobalTheory.T.arithHeightsAndForms_of_intersection_and_inductive hF hM
  have hC : ArChange := arChange_of_arMix hE hM
  ⟨hE, hC, GlobalTheory.T.arithSelfInter_constantShift_of_trivialWeightFormula hE hC, hM, GlobalTheory.T.arithInterProjectionFormula_of_heightProjectionFormula hP, arIso_holds, GlobalTheory.T.arithInterChangeOfMetric_of_mixedInductive hE hM⟩

end GlobalTheory.Published

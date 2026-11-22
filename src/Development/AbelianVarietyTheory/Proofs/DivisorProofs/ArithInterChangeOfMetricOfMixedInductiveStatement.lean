module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithInterChangeOfMetricOfMixedInductive
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithInterChangeOfMetric_of_mixedInductive : GlobalTheory.Published.ArExists → GlobalTheory.Published.ArMix → GlobalTheory.Published.ArMetric := by
  first | exact @GlobalTheory.Published.arMetric_of_arMix | exact GlobalTheory.Published.arMetric_of_arMix | (intros; apply GlobalTheory.Published.arMetric_of_arMix <;> assumption)

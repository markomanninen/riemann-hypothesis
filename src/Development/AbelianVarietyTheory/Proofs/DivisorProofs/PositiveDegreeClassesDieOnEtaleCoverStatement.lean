module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDegreeClassesDieOnEtaleCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover : GlobalTheory.EtC.A5 := by
  first | exact @GlobalTheory.EtC.classes_die_on_etale_cover | exact GlobalTheory.EtC.classes_die_on_etale_cover | (intros; apply GlobalTheory.EtC.classes_die_on_etale_cover <;> assumption)

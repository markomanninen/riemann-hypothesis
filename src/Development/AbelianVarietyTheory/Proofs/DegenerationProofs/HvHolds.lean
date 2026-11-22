module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

@[expose] public section

namespace GlobalTheory.Ex

theorem hv_holds : GlobalTheory.Ex.HV :=
  GlobalTheory.TestFibre.laws_all GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1

end GlobalTheory.Ex

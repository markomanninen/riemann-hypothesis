module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FiniteExtensionLangStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenLangRatFuncStatement

@[expose] public section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.NeedB

theorem tsen : Tsen := by
  intro k K _ _ _ _ _
  exact GlobalTheory.T.isFirstChernClass_of_finiteDimensional_of_forms_have_zeros (RatFunc k) K (GlobalTheory.T.exists_common_zero_homogeneous_ratFunc_of_mul_lt k)

end GlobalTheory.NeedB

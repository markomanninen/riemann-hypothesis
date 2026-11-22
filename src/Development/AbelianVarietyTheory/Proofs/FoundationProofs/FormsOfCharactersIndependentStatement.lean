module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FormsOfCharactersIndependent
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_mf_ch_sum_eq_zero : ∀ (k L N : ℕ) (a : DirichletCharacter ℂ N → ℕ → ℂ), 0 < L → N ∣ L → (∀ ε, MF k L (ch ε) (a ε)) → (∑ ε, a ε) = 0 → ∀ ε, a ε = 0 := by
  first | exact @GlobalTheory.EisM.Indep.forms_of_characters_independent | exact GlobalTheory.EisM.Indep.forms_of_characters_independent | (intros; apply GlobalTheory.EisM.Indep.forms_of_characters_independent <;> assumption)

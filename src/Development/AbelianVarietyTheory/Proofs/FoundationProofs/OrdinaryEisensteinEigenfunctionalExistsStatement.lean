module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinaryEisensteinEigenfunctionalExists
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinaryEisensteinEigenfunctional_exists : GlobalTheory.EisM.CuspidalUnitaryTwistsClaim := by
  first | exact @GlobalTheory.EisM.chapterM_holds | exact GlobalTheory.EisM.chapterM_holds | (intros; apply GlobalTheory.EisM.chapterM_holds <;> assumption)

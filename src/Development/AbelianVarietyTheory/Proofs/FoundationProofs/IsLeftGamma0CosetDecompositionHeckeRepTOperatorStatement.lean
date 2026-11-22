module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftGamma0CosetDecompositionHeckeRepTOperator
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepTOperator : ∀ L q : ℕ, q.Prime → ¬ q ∣ L → LRep L (DT L q) (repT q) := by
  first | exact @GlobalTheory.EisM.lRep_DT_repT | exact GlobalTheory.EisM.lRep_DT_repT | (intros; apply GlobalTheory.EisM.lRep_DT_repT <;> assumption)

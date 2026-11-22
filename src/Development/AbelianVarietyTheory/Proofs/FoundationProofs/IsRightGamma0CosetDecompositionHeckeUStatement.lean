module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsRightGamma0CosetDecompositionHeckeU
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRightGamma0CosetDecomposition_heckeU : ∀ L l : ℕ, 0 < L → l.Prime → l ∣ L → RRep L (DU L l) (fun j : Fin l => (repL L l (some j)).adjugate) := by
  first | exact @GlobalTheory.EisM.RightRepU.rrep | exact GlobalTheory.EisM.RightRepU.rrep | (intros; apply GlobalTheory.EisM.RightRepU.rrep <;> assumption)

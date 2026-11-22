module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslationLieConjugate
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_translation_lie_conjugate : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (g : GL (Fin a) (Cinf E)) (X : Lie E a), rt E a (infGL E a g) * lie E a X = lie E a (toL (g.val * Matrix.of X * (g⁻¹).val)) * rt E a (infGL E a g) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.rt_infGL_mul_lie | exact GlobalTheory.CompanionTheory.SmoothRep.rt_infGL_mul_lie | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.rt_infGL_mul_lie <;> assumption)

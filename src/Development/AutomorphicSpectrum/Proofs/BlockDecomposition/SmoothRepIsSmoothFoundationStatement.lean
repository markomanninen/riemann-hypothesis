module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothRepIsSmoothFoundation
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_rep_is_smooth_foundation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → GroundTheory.Automorphic.IsSmooth π := by
  first | exact @GlobalTheory.CompanionTheory.SmoothTransfer.isSmooth_found | exact GlobalTheory.CompanionTheory.SmoothTransfer.isSmooth_found | (intros; apply GlobalTheory.CompanionTheory.SmoothTransfer.isSmooth_found <;> assumption)

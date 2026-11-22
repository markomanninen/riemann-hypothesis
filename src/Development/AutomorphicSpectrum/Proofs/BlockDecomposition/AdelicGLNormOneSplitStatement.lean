module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicGLNormOneSplit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness

@[expose] public section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_GL_norm_one_split : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∃ e : GroundTheory.Automorphic.Reduction.normOneGL (K := E) (n := a) × ℝ ≃ₜ GA E a, ∀ x t, e (x, t) = splitCentre E a t * (x : GA E a) := by
  first | exact @GlobalTheory.CompanionTheory.SplitHomeo.exists_homeomorph | exact GlobalTheory.CompanionTheory.SplitHomeo.exists_homeomorph | (intros; apply GlobalTheory.CompanionTheory.SplitHomeo.exists_homeomorph <;> assumption)

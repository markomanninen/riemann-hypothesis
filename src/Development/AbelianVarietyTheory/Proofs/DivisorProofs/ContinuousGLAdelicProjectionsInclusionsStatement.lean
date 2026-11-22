module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGLAdelicProjectionsInclusions
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_GL_adelic_projections_inclusions : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), Continuous (fun g : GA E a => Matrix.GeneralLinearGroup.map (pInf E) g) ∧ Continuous (fun g : GA E a => Matrix.GeneralLinearGroup.map (pFin E) g) ∧ Continuous (infGL E a) ∧ Continuous (finGL E a) := by
  first | exact @GlobalTheory.GLProj.continuous_proj_incl | exact GlobalTheory.GLProj.continuous_proj_incl | (intros; apply GlobalTheory.GLProj.continuous_proj_incl <;> assumption)

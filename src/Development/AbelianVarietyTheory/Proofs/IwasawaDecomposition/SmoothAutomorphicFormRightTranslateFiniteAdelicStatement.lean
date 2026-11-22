module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAutomorphicFormRightTranslateFiniteAdelic
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothAutomorphicForm_rightTranslate_finiteAdelic : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFunSm θ V φ → ∀ k ∈ GfC V, IsAutFunSm θ V (rTr V k φ) := by
  first | exact @GlobalTheory.Mem.FinTranslate.isAutFunSm_rTr_fin | exact GlobalTheory.Mem.FinTranslate.isAutFunSm_rTr_fin | (intros; apply GlobalTheory.Mem.FinTranslate.isAutFunSm_rTr_fin <;> assumption)

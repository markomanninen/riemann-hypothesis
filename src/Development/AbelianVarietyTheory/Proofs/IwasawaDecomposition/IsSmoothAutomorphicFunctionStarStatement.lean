module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStar
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothAutomorphicFunction_star : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFunSm θ V φ → IsAutFunSm θ V (fun g => star (φ g)) := by
  first | exact @GlobalTheory.Mem.AutConj.isAutFunSm_star | exact GlobalTheory.Mem.AutConj.isAutFunSm_star | (intros; apply GlobalTheory.Mem.AutConj.isAutFunSm_star <;> assumption)

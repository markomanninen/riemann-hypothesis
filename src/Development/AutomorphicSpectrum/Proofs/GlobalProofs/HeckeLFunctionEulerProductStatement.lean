module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeLFunctionEulerProduct
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIdeleCircle

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_L_function_euler_product : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ) (s : ℂ), 1 < s.re → HasProd (eulerFactor χ s) ((toHecke χ hu).LFunction s) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBridge.hasProd_eulerFactor_toHecke | exact GlobalTheory.CompanionTheory.HeckeBridge.hasProd_eulerFactor_toHecke | (intros; apply GlobalTheory.CompanionTheory.HeckeBridge.hasProd_eulerFactor_toHecke <;> assumption)

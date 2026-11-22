module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivExpGLineEqRightDerivPow
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import GroundTheory.AutomorphicForms.DixmierMalliavin
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral

@[expose] public section

open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDeriv_expG_line_eq_foldr_rightDeriv : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (f : G → ℂ), h.IsSmoothFun f → ∀ (X : 𝔤) (g : G) (n : ℕ), ContDiff ℝ ∞ (fun t : ℝ => f (g * h.expG (t • X))) ∧ ∀ s : ℝ, iteratedDeriv n (fun t : ℝ => f (g * h.expG (t • X))) s = (List.replicate n X).foldr h.rightDeriv f (g * h.expG (s • X)) := by
  first | exact @GlobalTheory.iteratedDeriv_expG_line_eq_rightDeriv_pow | exact GlobalTheory.iteratedDeriv_expG_line_eq_rightDeriv_pow | (intros; apply GlobalTheory.iteratedDeriv_expG_line_eq_rightDeriv_pow <;> assumption)

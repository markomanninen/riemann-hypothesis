module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
public import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormNatCastOfCoprime

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

namespace GlobalTheory

theorem locBasisW_clear_den : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ρ : D.host.E →+* ℂ_[p]) (N N' : ℕ) (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : Matrix (Fin N) (Fin N) D.host.E) (P' : Matrix (Fin N') (Fin N') D.host.E), L₁.FG → TaylorLogMetric.EqAt D p L L₁ → TaylorLogMetric.EqAt D p L' L₁' → TaylorLogMetric.LocBasisW D ρ L P → TaylorLogMetric.LocBasisW D ρ L' P' → ∃ σ σ' : 𝓞 D.host.E, ‖ρ (σ : D.host.E)‖ = 1 ∧ ‖ρ (σ' : D.host.E)‖ = 1 ∧ (∀ (a : Fin N) (x : Fin N → D.host.E), x ∈ L₁ → ∃ o : 𝓞 D.host.E, (o : D.host.E) = (σ : D.host.E) * ∑ j, P⁻¹ a j * x j) ∧ ∀ b : Fin N', (fun i => (σ' : D.host.E) * P' i b) ∈ L₁' := by
  first
  | exact @_root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers
  | exact _root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers
  | (apply _root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers ..)

end GlobalTheory

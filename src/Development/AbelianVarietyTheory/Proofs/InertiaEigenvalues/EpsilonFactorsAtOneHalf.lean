module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import GroundTheory.LocalFields.LocalZetaGauss

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DelEps.GaussBridge

open GroundTheory.LocalField (valBall unitFiltrationUnits addCharConductor quasiCharConductor
  IsUnramifiedChar unifUnit unitsModRep unitsModFiltration unitsModCoset gaussSum)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem continuous_of_isSmoothChar {χ : Fˣ →* ℂˣ} (hχ : IsSmoothChar χ) : Continuous χ := by
  refine continuous_def.2 fun U _ => isOpen_iff_forall_mem_open.2 fun x hx => ?_
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (χ.ker : Set Fˣ), fun y hy => ?_,
    hχ.preimage (continuous_const_mul _), by simp⟩
  have h : χ (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  show χ y ∈ U
  rw [← h]
  exact hx

variable {χ : Fˣ →* ℂˣ} {ψ : AddChar F Circle}

end GlobalTheory.DelEps.GaussBridge


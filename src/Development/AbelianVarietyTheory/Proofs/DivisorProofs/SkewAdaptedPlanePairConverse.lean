module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharDotMulMemAdelicSchwartzSpaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairRestrictionThetaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerExtensionStatement

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EvZeroUniq

open scoped Classical

theorem proj_zero_mem_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AF F) i).1) = 0 := by
    funext i
    exact map_zero _
  have h2 : (fun i => ((0 : κ → AF F) i).2) = 0 := rfl
  show pureA F f g 0 = _
  rw [pureA, h1, h2]
  simp [mul_comm]

theorem schr_mem_schA {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : schr ψ w Φ ∈ schA F κ := by
  have h2 := GlobalTheory.T.addCharDotMul_mem_adelicSchwartzSpace ψ hψ w.2 _ (GlobalTheory.SchwartzTranslate.main F κ w.1 Φ hΦ)
  have : schr ψ w Φ = ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) • (fun x => ψ (x ⬝ᵥ w.2) * Φ (x + w.1)) := by
    funext x
    simp only [schr, Pi.smul_apply, smul_eq_mul, AddChar.map_add_eq_mul]
    ring
  rw [this]
  exact Submodule.smul_mem _ _ h2

theorem apply_eq_rho {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {Bf : W → W → AF F} {κ : Type} [Fintype κ] (dc : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (f : (κ → AF F) → ℂ)
    (x : κ → AF F) : f x = dc.rho ψ (dc.e.symm (x, 0)) f 0 := by
  simp [Darboux.rho, schr]

theorem rho_apply_zero {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {Bf : W → W → AF F} {κ : Type} [Fintype κ] (dc : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (f : (κ → AF F) → ℂ)
    (z : W) (hz : (dc.e z).1 = 0) : dc.rho ψ z f 0 = f 0 := by
  simp [Darboux.rho, schr, hz]

end GlobalTheory.EvZeroUniq

module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsOrbitProd

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.FunExt

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FunExt.ConjLift

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Field Ω] [Algebra K Ω] [Algebra L Ω]

theorem mem_Dec_of_iff {F : Type} [Field F] [NumberField F] [Algebra F Ω] {A : ValuationSubring Ω} {σ : G F Ω}
    (hσ : ∀ x, σ x ∈ A ↔ x ∈ A) : σ ∈ Dec (F := F) A := by
  rw [mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hσ]
  show (σ * σ⁻¹) x ∈ A ↔ x ∈ A
  rw [mul_inv_cancel]; rfl

variable (s : L ≃ₐ[K] L) (g : G K Ω) (hgs : ∀ x : L, g (algebraMap L Ω x) = algebraMap L Ω (s x))
include hgs


variable {A : ValuationSubring Ω}

omit hgs

end GlobalTheory.FunExt.ConjLift

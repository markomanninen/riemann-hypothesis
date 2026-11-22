module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.AdelicPlaneLevi

open Matrix

section Gen

variable {R : Type} [CommRing R] {n : ℕ} (c : R →+* R) (J : Matrix (Fin n) (Fin n) R)

def fR (u v : Fin n → R) : R := u ⬝ᵥ J *ᵥ (fun i => c (v i))

variable {c J}
variable {x y : Fin n → R} (hxx : fR c J x x = 0) (hyy : fR c J y y = 0) (hxy : fR c J x y = 1)
  (hyx : fR c J y x = -1)
include hxx hyy hxy hyx

end Gen

end GlobalTheory.AdelicPlaneLevi

namespace GlobalTheory.AdelicPlaneLevi

open Matrix

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_cA (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (a : AE F E) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [cA, hσ]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem sigma_invol {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]

end Main

end GlobalTheory.AdelicPlaneLevi

end

module

public import Mathlib

@[expose] public section

open NumberField IsDedekindDomain TensorProduct

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IdeleNormTraceForm

abbrev Af : Type := FiniteAdeleRing (𝓞 ℚ) ℚ

def Zhat : Subring Af where
  carrier := {a | ∀ v : HeightOneSpectrum (𝓞 ℚ), a v ∈ v.adicCompletionIntegers ℚ}
  mul_mem' := fun {a b} ha hb v => (v.adicCompletionIntegers ℚ).mul_mem _ _ (ha v) (hb v)
  one_mem' := fun v => (v.adicCompletionIntegers ℚ).one_mem
  add_mem' := fun {a b} ha hb v => (v.adicCompletionIntegers ℚ).add_mem _ _ (ha v) (hb v)
  zero_mem' := fun v => (v.adicCompletionIntegers ℚ).zero_mem
  neg_mem' := fun {a} ha v => (v.adicCompletionIntegers ℚ).neg_mem _ (ha v)

def ZhatUnits : Subgroup Afˣ := Zhat.toSubmonoid.units

abbrev Adelic (V : Type) [AddCommGroup V] [Module ℚ V] : Type := Af ⊗[ℚ] V

def ideleNorm (K : Type) [Field K] [NumberField K] : (Adelic K)ˣ →* Afˣ :=
  Units.map (Algebra.norm Af : Adelic K →* Af)

def ratIdele : ℚˣ →* Afˣ := Units.map (algebraMap ℚ Af : ℚ →+* Af).toMonoidHom

def IsNormScale {K : Type} [Field K] [NumberField K] (s : (Adelic K)ˣ) (q : ℚˣ) : Prop :=
  0 < (q : ℚ) ∧ (ideleNorm K s)⁻¹ * ratIdele q ∈ ZhatUnits

section Groups

variable (E : Type) [Field E] [NumberField E]
variable {W : Type} [AddCommGroup W] [Module ℚ W] [Module E W] [IsScalarTower ℚ E W]

def IsHermitian [IsCMField E] (h : W →ₗ[ℚ] W →ₗ[ℚ] E) : Prop :=
  (∀ (a : E) (x y : W), h (a • x) y = a * h x y) ∧
    ∀ x y : W, h y x = IsCMField.complexConj E (h x y)

def traceForm (ξ₀ : E) (h : W →ₗ[ℚ] W →ₗ[ℚ] E) : LinearMap.BilinForm ℚ W :=
  h.compr₂ (Algebra.trace ℚ E ∘ₗ LinearMap.mulLeft ℚ ξ₀)



variable [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

end Groups

end GlobalTheory.IndefiniteRowSideFullHecke.IdeleNormTraceForm

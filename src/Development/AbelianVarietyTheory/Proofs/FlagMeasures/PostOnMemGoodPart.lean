module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsCuspHom
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicRightTranslateFinite

@[expose] public section

noncomputable section

open Formalism.MainNotions.ArithmeticCylinders IsDedekindDomain MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultTranslate

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
  {θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

theorem isCuspFun_rTr {φ : GA D V → ℂ} (h : IsCuspFun V φ) (x : GA D V) : IsCuspFun V (rTr V x φ) := by
  intro r C hC μ 𝓕 hμ h𝓕 g
  simpa only [rTr, mul_assoc] using h r C hC μ 𝓕 hμ h𝓕 (g * x)

theorem isMultMap_rTr {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} {x : GA D V} (hx : x ∈ GfC V)
    (hJ : ∀ k ∈ J', x⁻¹ * k * x ∈ J ∧ χ' k = χ (x⁻¹ * k * x)) {T : MMap M} (h : IsMultMap θ M J χ T) :
    IsMultMap θ M J' χ' (postOn M (GlobalTheory.FinTranslate.rTrL V x) T) := by
  constructor
  · intro v
    exact GlobalTheory.FinTranslate.isAutFunSm_rTr θ V x hx _ (h.aut v)
  · intro v
    exact isCuspFun_rTr (h.cusp v) x
  · intro v k hk g
    change T v (g * k * x) = χ' k * T v (g * x)
    rw [(hJ k hk).2, ← h.lev v _ (hJ k hk).1]
    group
  · intro τ g hg v w hw
    funext y
    change T (Function.update v τ w) (y * x) = T v (y * atTau θ V τ g * x)
    rw [h.equiv τ g hg v w hw, mul_assoc,
      ← GlobalTheory.FinTranslate.comm_fin_real V hx (GlobalTheory.FinTranslate.atTau_mem θ V τ g), ← mul_assoc]
    rfl
  · intro τ v y
    exact h.cont τ v (y * x)

theorem postOn_mem_goodPart {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} {x : GA D V} (hx : x ∈ GfC V)
    (hJ : ∀ k ∈ J', x⁻¹ * k * x ∈ J ∧ χ' k = χ (x⁻¹ * k * x)) {L L' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)}
    (hL : ∀ f, L' (rTr V x f) = rTr V x (L f)) {T : MMap M} (h : T ∈ goodPart θ M J χ L) :
    postOn M (GlobalTheory.FinTranslate.rTrL V x) T ∈ goodPart θ M J' χ' L' := by
  rw [mem_goodPart, GlobalTheory.MultMem.mem_mult_iff] at h ⊢
  refine ⟨isMultMap_rTr hx hJ h.1, fun v => ?_⟩
  change L' (rTr V x (T v)) = rTr V x (T v)
  rw [hL, h.2]

end GlobalTheory.MultTranslate

end

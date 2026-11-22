module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClmThetaSumRhoPure

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeMeasV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end GlobalTheory.ConeMeasV

namespace GlobalTheory.ConeMeasV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem comp_ev_mem_adm {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    {B : Base F E} {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
    {I : Set (Matrix (Fin n) (Fin d) (AE F E))} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁}
    (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (hE : IsEv B M M₁ ι ι' I e)
    {l : Fn F n₁ d₁ →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁)) :
    l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  have key := GlobalTheory.SBSpan.mem_span_restrictedProd F (Fin n × Fin d) g hg
  clear hg
  induction key using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨φ, h1, h2, rfl⟩ := hp
    have hvac : ∀ᶠ v in cofinite, φ v = M.vac v := (h2.and hM.std).mono fun v h => h.1.trans h.2.symm
    have hψSB : ∀ v, ev v (φ v) ∈ SB (Fin n₁ × Fin d₁ → Fv F v) := fun v =>
      (hev v).2 ▸ Submodule.mem_map_of_mem (h1 v)
    have hψstd : ∀ᶠ v in cofinite, ev v (φ v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
      (hvac.and hM₁.std).mono fun v h => by rw [h.1, (hev v).1, h.2]
    obtain ⟨T, hT⟩ := hl _ ⟨isLocallyConstant_finprod_evalV _ hψSB hψstd,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ hψSB hψstd⟩
    refine ⟨T.comp ei, fun f => ?_⟩
    have h := hloc f φ h1 hvac
    rw [LinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hT]
    exact congrArg l h
  | zero =>
    refine ⟨0, fun f => ?_⟩
    have : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) 0 = 0 := by
      funext x; simp [pureA]
    rw [this, map_zero, ContinuousLinearMap.zero_apply]
  | add p q _ _ hp hq =>
    obtain ⟨T₁, h₁⟩ := hp
    obtain ⟨T₂, h₂⟩ := hq
    refine ⟨T₁ + T₂, fun f => ?_⟩
    have : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) (p + q) = pureA F f p + pureA F f q := by
      funext x; simp [pureA, mul_add]
    rw [this, map_add (f := _), h₁, h₂, ContinuousLinearMap.add_apply]
  | smul c p _ hp =>
    obtain ⟨T, hT⟩ := hp
    refine ⟨c • T, fun f => ?_⟩
    have : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) (c • p) = c • pureA F f p := by
      funext x; simp [pureA]; ring
    rw [this, map_smul, hT, ContinuousLinearMap.smul_apply]

def schrLin {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) :
    ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun Φ := schr ψ w Φ
  map_add' Φ Ψ := by funext x; simp [schr, mul_add]
  map_smul' c Φ := by funext x; simp [schr]; ring

theorem schrLin_apply {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F))
    (Φ : (κ → AF F) → ℂ) : schrLin ψ w Φ = schr ψ w Φ := rfl

theorem schr_mem_schA {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F))
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : schr ψ w Φ ∈ schA F κ := by
  have : schA F κ ≤ (schA F κ).comap (schrLin ψ w) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    obtain ⟨T, g', hg', hT⟩ := GlobalTheory.ThetaHeisCLM.exists_schr_pureA_eq ψ hψ w hg
    show schrLin ψ w (pureA F f g) ∈ schA F κ
    rw [schrLin_apply, hT]
    exact Submodule.subset_span ⟨T f, g', hg', rfl⟩
  exact this hΦ

theorem comp_schr_mem_adm {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F))
    {l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ) : l ∘ₗ schrLin ψ w ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, g', hg', hT⟩ := GlobalTheory.ThetaHeisCLM.exists_schr_pureA_eq ψ hψ w hg
  obtain ⟨L, hL⟩ := hl g' hg'
  refine ⟨L.comp T, fun f => ?_⟩
  rw [LinearMap.comp_apply, schrLin_apply, hT, hL, ContinuousLinearMap.comp_apply]

end GlobalTheory.ConeMeasV

namespace GlobalTheory.ConeMeasV

end GlobalTheory.ConeMeasV

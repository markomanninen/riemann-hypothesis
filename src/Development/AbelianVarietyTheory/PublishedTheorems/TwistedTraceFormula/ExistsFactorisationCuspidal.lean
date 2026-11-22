module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.AutMult
open Formalism.MainNotions.KudlaSiegelWeil (Restr)
open Formalism.MainNotions.SchurIrreducible (Pl)
open GlobalTheory.PRep (IsAdmissible fixed)
open scoped InnerProductSpace

namespace GlobalTheory

namespace Flath

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

abbrev finFactor (R : ∀ v, IrrU (GPl σ J v)) (v : HeightOneSpectrum (𝓞 F)) :
    GLoc σ J v →* ((R (.inr v)).H →L[ℂ] (R (.inr v)).H) := (R (.inr v)).π

def IsUnramFactorisation {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (R : ∀ v, IrrU (GPl σ J v))
    (ξ : ∀ v, (R v).H) (π : GAd σ J →* (H →L[ℂ] H)) (B : (∀ v, (R v).H) → H) : Prop :=
  IsFactorisation σ J (fun v => (R v).π) ξ π B ∧
  (∀ v, (smRep (finFactor R v)).IsIrreducible ∧ IsAdmissible (smRep (finFactor R v))) ∧
  ∀ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L →
    ∀ᶠ v in cofinite, fixed (toRep (finFactor R v)) (stabLoc σ J L v) = ℂ ∙ ξ (.inr v)

end Flath

namespace Published

def FlathFactorisation : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GAd σ J →* (H →L[ℂ] H)), IsIrrUnitary π →
        ∃ (R : ∀ v, IrrU (GPl σ J v)) (ξ : ∀ v, (R v).H) (B : (∀ v, (R v).H) → H), Flath.IsUnramFactorisation R ξ π B

namespace FlathFactorisation

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {π : GAd σ J →* (H →L[ℂ] H)} {π' : GAd σ J →* (H' →L[ℂ] H')}

theorem exists_hasCompPl (h : FlathFactorisation) (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hπ : IsIrrUnitary π)
    (v : Pl F) : ∃ δ : IrrU (GPl σ J v), HasCompPl σ J v δ.π π :=
  let ⟨R, _, _, hR⟩ := h F E σ hc n J hJ H π hπ
  ⟨R v, hR.1.hasCompPl v⟩

end General

section Space

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exists_factorisation (h : FlathFactorisation) {π : GA D V →* (H →L[ℂ] H)} (hπ : IsIrrUnitary π) :
    ∃ (R : ∀ v, IrrU (GPl D.sp.cm.sig V.gram v)) (ξ : ∀ v, (R v).H) (B : (∀ v, (R v).H) → H),
      Flath.IsUnramFactorisation R ξ π B ∧
        ∀ᶠ v in cofinite, fixed (toRep (Flath.finFactor R v)) (Kv V v) = ℂ ∙ ξ (.inr v) :=
  let ⟨R, ξ, B, hR⟩ := h _ _ _ (isCMExt_host D) _ _ (GlobalTheory.Mem.VolExists.isHermND D.sp.cm V) H π hπ
  ⟨R, ξ, B, hR, hR.2.2 _ (SelfDual.isLattice_frameLat V)⟩

end Space

end FlathFactorisation

end Published

namespace Flath

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem smRep_charRep {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {χ : G →* Circle}
    (h : IsOpen (χ.ker : Set G)) : (smRep (charRep χ)).IsIrreducible ∧ IsAdmissible (smRep (charRep χ)) := by
  have ht : PRep.smoothPart (toRep (charRep χ)) = ⊤ := eq_top_iff.2 fun z _ => by
    refine isOpen_iff_mem_nhds.2 fun g hg => mem_of_superset
      ((h.preimage (continuous_const_mul g⁻¹)).mem_nhds (by simp)) fun x hx => ?_
    have e : χ x = χ g := by
      have : χ (g⁻¹ * x) = 1 := hx
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm
    change (χ x : ℂ) • z = z
    rw [e]
    exact hg
  have h1 : Module.finrank ℂ (PRep.smoothPart (toRep (charRep χ))) = 1 := by rw [ht, finrank_top, Module.finrank_self]
  have := isSimpleModule_iff_finrank_eq_one.2 h1
  have hs : IsSimpleOrder (Submodule ℂ (PRep.smoothPart (toRep (charRep χ)))) := inferInstance
  have : Nontrivial (Subrepresentation (smRep (charRep χ))) :=
    ⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e :)⟩
  exact ⟨⟨fun S => (eq_bot_or_eq_top S.toSubmodule).imp (fun e => Subrepresentation.toSubmodule_injective e)
    fun e => Subrepresentation.toSubmodule_injective e⟩, isSmooth_smoothRep _, fun _ _ _ => inferInstance⟩

theorem isUnramFactorisation_charRep (χ : ∀ v, GPl σ J v →* Circle) (hχ : ∀ v, Continuous (χ v))
    (ho : ∀ v, IsOpen ((χ (.inr v)).ker : Set (GPl σ J (.inr v)))) (ψ : GAd σ J →* Circle)
    (h : ∀ g, ∀ᶠ v in cofinite, χ v (projPl σ J v g) = 1) (hψ : ∀ g, (ψ g : ℂ) = ∏ᶠ v, (χ v (projPl σ J v g) : ℂ)) :
    IsUnramFactorisation (fun v => IrrU.ofChar (χ v) (hχ v)) (fun _ => (1 : ℂ)) (charRep ψ)
      fun y : Pl F → ℂ => ∏ᶠ v, y v := by
  have hf : IsFactorisation σ J (fun v => charRep (χ v)) (fun _ => 1) (charRep ψ) fun y => ∏ᶠ v, y v :=
    isRestrTensor_charRep (projPl σ J) χ ψ h hψ
  refine ⟨hf, fun v => smRep_charRep (G := GLoc σ J v) (ho v), fun L _ => (hf.eventually_fixed L).mono fun v hv => ?_⟩
  refine le_antisymm (fun z _ => Submodule.mem_span_singleton.2 ⟨z, mul_one (z : ℂ)⟩)
    ((Submodule.span_singleton_le_iff_mem _ _).2 (LGrp.mem_fixed.2 hv))

end Flath

end GlobalTheory

end

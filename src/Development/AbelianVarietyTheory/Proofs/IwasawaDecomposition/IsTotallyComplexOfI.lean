module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisSubfieldConjStable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetTypeNormPrincipal
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsBaseTwoWords

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem.BaseEx

section ext

variable {K K' : Type} [Field K] [Field K'] (f : K →+* K')

end ext

section host

variable {R : Ranks} (H : Host R)

theorem conjugate_emb (g : R.GG) :
    ComplexEmbedding.conjugate (H.emb g) = H.emb (g * R.cc) := by
  rw [Formalism.L2.Geo.emb_mul_cc_comp]
  refine RingHom.ext fun x => ?_
  have hcm := H.isCMField_hostE
  have h : IsCMField.complexConj H.E x = H.conj x := by
    apply H.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  show starRingEnd ℂ (H.emb g x) = H.emb g (H.conj x)
  rw [← h, IsCMField.complexEmbedding_complexConj]

theorem ex_emb_iff (g : R.GG) :
    (∃ t : Tau R, H.emb t = H.emb g) ↔ g ∈ R.Psi :=
  ⟨fun ⟨t, ht⟩ => (factEmb R H).1.1 ht ▸ t.2, fun h => ⟨⟨g, h⟩, rfl⟩⟩

theorem emb_cm (σ : H.E →+* ℂ) :
    (∃ t : Tau R, H.emb t = σ) ↔ ¬ ∃ t : Tau R, H.emb t = ComplexEmbedding.conjugate σ := by
  obtain ⟨g, rfl⟩ := (factEmb R H).1.2 σ
  rw [conjugate_emb, ex_emb_iff, ex_emb_iff]
  exact Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g

theorem sum_emb_bijective : Function.Bijective
    (Sum.elim (fun t : Tau R => H.emb t) fun t : Tau R => ComplexEmbedding.conjugate (H.emb t)) := by
  have hc : ∀ σ : H.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    fun σ => star_star σ
  have hi : ∀ {a b : Tau R}, H.emb a = H.emb b → a = b := fun h => Subtype.ext ((factEmb R H).1.1 h)
  constructor
  · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · rw [hi h]
    · exact absurd ⟨a, h⟩ ((emb_cm H (H.emb b)).1 ⟨b, rfl⟩)
    · exact absurd ⟨b, h.symm⟩ ((emb_cm H (H.emb a)).1 ⟨a, rfl⟩)
    · have := congrArg ComplexEmbedding.conjugate h
      rw [hc, hc] at this
      rw [hi this]
  · intro σ
    by_cases h : ∃ t : Tau R, H.emb t = ComplexEmbedding.conjugate σ
    · obtain ⟨t, ht⟩ := h
      exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
    · obtain ⟨t, ht⟩ := (emb_cm H σ).2 h
      exact ⟨Sum.inl t, ht⟩


end host

end GlobalTheory.Mem.BaseEx

end

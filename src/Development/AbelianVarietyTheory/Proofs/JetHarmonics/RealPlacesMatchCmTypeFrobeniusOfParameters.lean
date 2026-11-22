module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConjCmHostRootNeSelf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceLabelBijectiveCardEqF
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotDvdDiscrHost
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ComapLiesOver

@[expose] public section

set_option autoImplicit false

namespace GlobalTheory.GoodDepth

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem placeTie_of_pins : ∀ (D : D7) (L : SizeData₂ D) (T : Core D), T.Q.Pins →
    PlaceTie (numOf D L) T.Q.c (fun z => DV.tauEmb D (plOf D z)) := by
  intro D L T hp
  have hh := hp.1
  refine ⟨?_, ?_, hh.1, D.host.hostE_isGalois, ?_, ?_, ?_⟩
  · intro z z' h
    exact (plOf_bijective_card D).1.1 (D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h)))
  · intro τ
    constructor
    · intro hτ
      have hex : ∃ t : D.what₂.Tau, τ = DV.tauEmb D t := by
        obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 τ
        by_cases hgP : g ∈ D.R.Psi
        · obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D g).2 hgP
          exact ⟨t, hg.symm.trans ht⟩
        · exfalso
          have h2 : g * D.R.cc ∈ D.R.Psi := by
            by_contra h
            exact hgP ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g).2 h)
          obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D (g * D.R.cc)).2 h2
          have h3 : DV.tauEmb D t (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hh.2.2.2 t
          rw [← ht, Formalism.L2.Geo.emb_mul_cc_comp, hg, RingHom.comp_apply] at h3
          have h4 : τ (D.host.conj (T.Q.H.rt : D.host.E)) = star (τ (T.Q.H.rt : D.host.E)) := Formalism.MainNotions.WeightFamilies.emb_conj D τ _
          have hτ' : τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hτ
          have hc : (starRingEnd ℂ) T.Q.H.rt0 ≠ T.Q.H.rt0 := by
            intro he
            obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 he
            have hs := T.Q.H.sqrt_neg_disc_sq
            rw [hx] at hs
            have hs' : x ^ 2 = -(T.Q.H.d : ℝ) := by exact_mod_cast hs
            have hd : (0 : ℝ) < T.Q.H.d := by exact_mod_cast T.Q.H.d_prime.pos
            nlinarith [sq_nonneg x]
          apply hc
          calc star T.Q.H.rt0 = star (τ (T.Q.H.rt : D.host.E)) := by rw [hτ']
            _ = τ (D.host.conj (T.Q.H.rt : D.host.E)) := h4.symm
            _ = T.Q.H.rt0 := h3
      obtain ⟨t, ht⟩ := hex
      obtain ⟨z, hz⟩ := (plOf_bijective_card D).1.2 t
      exact ⟨z, by rw [ht, ← hz]⟩
    · rintro ⟨z, rfl⟩
      exact hh.2.2.2 _
  · intro σ τ
    exact D.host.galE_injective (by
      rw [D.host.galE_mul, D.host.galE_mul, mul_comm])
  · intro p hp h2 hq hd
    exact GlobalTheory.GoodDepth.not_dvd_discr_host D.R D.host p hp h2 hq hd
  · intro la hla z x
    exact GlobalTheory.FrobPlace.frob_place D L T.Q.H _ T.Q.c la hla z x

end GlobalTheory.GoodDepth

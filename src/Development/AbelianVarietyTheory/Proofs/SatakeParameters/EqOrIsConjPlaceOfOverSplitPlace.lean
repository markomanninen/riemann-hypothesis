module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitPlaceOver

theorem host_conj_eq' (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

theorem eq_or_isConjPl : ∀ (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host), NG.OverPl w s.v →
    s.w = w ∨ IsConjPl D.host w s.w := by
  intro D s w hov
  let cO := IsCMField.ringOfIntegersComplexConj D.host.E
  have cc (x : 𝓞 D.host.E) : cO (cO x) = x := by
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, IsCMField.coe_ringOfIntegersComplexConj]
    exact IsCMField.complexConj_apply_apply D.host.E (x : D.host.E)
  let Q : PlE D.host := {
    asIdeal := s.w.asIdeal.comap (cO : 𝓞 D.host.E →+* 𝓞 D.host.E)
    isPrime := Ideal.comap_isPrime _ _
    ne_bot := by
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot s.w.ne_bot
      refine (Submodule.ne_bot_iff _).2 ⟨cO y, ?_, ?_⟩
      · show (cO : 𝓞 D.host.E →+* 𝓞 D.host.E) (cO y) ∈ s.w.asIdeal
        rw [RingHom.coe_coe, cc]; exact hy
      · intro h0
        apply hy0
        rw [← cc y, h0, map_zero] }
  have hQ (x : 𝓞 D.host.E) : x ∈ Q.asIdeal ↔ cO x ∈ s.w.asIdeal := Iff.rfl
  have he : w = s.w ∨ w = Q := by
    by_contra hne
    push Not at hne
    obtain ⟨h1, h2⟩ := hne
    have nle : ∀ P : PlE D.host, w ≠ P → ¬ w.asIdeal ≤ P.asIdeal := fun P h hle =>
      h (HeightOneSpectrum.ext (w.isMaximal.eq_of_le P.isPrime.ne_top hle))
    obtain ⟨a, ha, haP⟩ := Set.not_subset.mp (nle s.w h1)
    obtain ⟨b, hb, hbQ⟩ := Set.not_subset.mp (nle Q h2)
    have key : ∃ x ∈ w.asIdeal, x ∉ s.w.asIdeal ∧ x ∉ Q.asIdeal := by
      by_cases haQ : a ∈ Q.asIdeal
      · by_cases hbP : b ∈ s.w.asIdeal
        · refine ⟨a + b, w.asIdeal.add_mem ha hb, fun h => haP ?_, fun h => hbQ ?_⟩
          · simpa using s.w.asIdeal.sub_mem h hbP
          · simpa using Q.asIdeal.sub_mem h haQ
        · exact ⟨b, hb, hbP, hbQ⟩
      · exact ⟨a, ha, haP, haQ⟩
    obtain ⟨x, hx, hxP, hxQ⟩ := key
    rw [hQ] at hxQ
    have hfix : cO (x * cO x) = x * cO x := by rw [map_mul, cc, mul_comm]
    obtain ⟨y, hy⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).1 hfix
    have hyw : y ∈ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
      rw [Ideal.mem_comap, hy]; exact w.asIdeal.mul_mem_right _ hx
    rw [hov.trans s.w_under.symm, Ideal.mem_comap, hy] at hyw
    rcases s.w.isPrime.mem_or_mem hyw with h | h
    · exact hxP h
    · exact hxQ h
  rcases he with e | e
  · exact Or.inl e.symm
  · right
    intro x y hxy
    have hy : y = cO x := by
      apply RingOfIntegers.ext
      rw [hxy, IsCMField.coe_ringOfIntegersComplexConj, host_conj_eq']
    rw [e, hQ, hy]

end GlobalTheory.SplitPlaceOver

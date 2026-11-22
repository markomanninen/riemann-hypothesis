module

public import ReciprocityTheory.DualLattices.NsetExpInjectiveSurjective

@[expose] public section

noncomputable section

open PowerSeries

namespace ReciprocityTheory.PGsh

namespace TowerExample

variable (p : ℕ) [Fact p.Prime]

lemma ne_top (m : ℕ) (hm : 0 < m) : Ideal.span {(X : (ZMod p)⟦X⟧) ^ m} ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top, PowerSeries.isUnit_iff_constantCoeff]
  simp [zero_pow hm.ne']

lemma isLocalHom_of_surj {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [Nontrivial S]
    (f : R →+* S) (hf : Function.Surjective f) : IsLocalHom f := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  obtain ⟨c, hc⟩ := hf (↑ha.unit⁻¹ : S)
  have hker : RingHom.ker f ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
  have h1 : 1 - a * c ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, RingHom.map_sub, map_one, map_mul, hc, IsUnit.mul_val_inv, sub_self]
  have h2 : a * c ∈ IsLocalRing.maximalIdeal R :=
    Ideal.mul_mem_right c _ ((IsLocalRing.mem_maximalIdeal a).2 hna)
  have h3 := Ideal.add_mem _ (hker h1) h2
  rw [sub_add_cancel] at h3
  exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal R).ne_top h3

end TowerExample


end ReciprocityTheory.PGsh

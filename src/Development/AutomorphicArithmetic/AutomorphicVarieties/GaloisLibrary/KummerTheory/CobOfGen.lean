module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoboundaryOfGenerator

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.cobOfGen :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (χ : Γ →* ℤ_[l]ˣ) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (γ : Γ),
    Continuous χ → ContAction ρ → (∀ g, χ g = 1 → ∀ m, ρ g m = m) → (∀ g, χ g ∈ (Subgroup.zpowers (χ γ)).topologicalClosure) → (Function.Surjective fun m => ρ γ m - m) →
    ∀ z ∈ Z1 ρ, (∀ g, χ g = 1 → z g = 0) → z ∈ B1 ρ := by
  intro l _ Γ _ _ _ _ χ R M _ _ _ _ _ ρ γ hχ hρ hker hgen hsurj z hz hz0
  have hzc : Continuous z := hz.1
  have hzm : ∀ g h : Γ, z (g * h) = z g + ρ g (z h) := hz.2
  obtain ⟨m, hm⟩ := hsurj (z γ)
  have hm' : ρ γ m - m = z γ := hm
  have hone : z 1 = 0 := hz0 1 (map_one χ)
  let S : Subgroup Γ :=
    { carrier := {g | z g = ρ g m - m}
      one_mem' := by
        change z 1 = ρ 1 m - m
        simp [hone]
      mul_mem' := by
        intro a b ha hb
        have ha' : z a = ρ a m - m := ha
        have hb' : z b = ρ b m - m := hb
        change z (a * b) = ρ (a * b) m - m
        rw [hzm, ha', hb', map_mul, map_sub, Module.End.mul_apply]
        abel
      inv_mem' := by
        intro a ha
        have ha' : z a = ρ a m - m := ha
        change z a⁻¹ = ρ a⁻¹ m - m
        have h1 := hzm a⁻¹ a
        have h2 : ρ a⁻¹ (ρ a m) = m := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rw [inv_mul_cancel, hone, ha', map_sub, h2] at h1
        rw [eq_neg_of_add_eq_zero_left h1.symm, neg_sub] }
  have hρm : Continuous fun g : Γ => ρ g m :=
    Continuous.comp (g := fun p : Γ × M => ρ p.1 p.2) (f := fun g : Γ => (g, m)) hρ
      (continuous_id.prodMk continuous_const)
  have hSc : IsClosed (S : Set Γ) := isClosed_eq hzc (hρm.sub continuous_const)
  have himg : IsClosed ((S.map χ : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_map]
    exact (hSc.isCompact.image hχ).isClosed
  have hle : (Subgroup.zpowers (χ γ)).topologicalClosure ≤ S.map χ :=
    Subgroup.topologicalClosure_minimal _
      ((Subgroup.zpowers_le).2 ⟨γ, hm'.symm, rfl⟩) himg
  have hall : ∀ g : Γ, g ∈ S := by
    intro g
    obtain ⟨s, hs, hsg⟩ := hle (hgen g)
    have hk : χ (s⁻¹ * g) = 1 := by rw [map_mul, map_inv, hsg, inv_mul_cancel]
    have hmem : s⁻¹ * g ∈ S := by
      change z (s⁻¹ * g) = ρ (s⁻¹ * g) m - m
      rw [hz0 _ hk, hker _ hk, sub_self]
    simpa using S.mul_mem hs hmem
  refine ⟨m, funext fun g => ?_⟩
  exact (hall g).symm


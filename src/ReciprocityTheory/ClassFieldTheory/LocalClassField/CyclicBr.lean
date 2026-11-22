module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Herbrand
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrand
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsG
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RestrictedMultiplicativeH1Subsingleton
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.FinCoh

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

@[reducible] def commGroupOfZpowers {G : Type*} [inst : Group G] (g₀ : G) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) :
    CommGroup G :=
  { inst with
    mul_comm := fun a b => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg b)
      rw [← zpow_add, ← zpow_add, add_comm] }

theorem nonempty_H_odd {R G : Type} [CommRing R] [Group G] [Fintype G] [TopologicalSpace G]
    [IsTopologicalGroup G] [DiscreteTopology G] (M : TRep R G) (g₀ : G) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (i : ℕ) (hi : Odd i) :
    Nonempty (M.H i ≃+ Herbrand.H1 M.rho g₀) := by
  let _ : CommGroup G := commGroupOfZpowers g₀ hg
  obtain ⟨e⟩ := Herbrand.nonempty_groupCohomology_odd M.rho g₀ hg i hi
  exact ⟨(finEquiv M i).toAddEquiv.trans e⟩

theorem nonempty_H_even {R G : Type} [CommRing R] [Group G] [Fintype G] [TopologicalSpace G]
    [IsTopologicalGroup G] [DiscreteTopology G] (M : TRep R G) (g₀ : G) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (i : ℕ) (h0 : i ≠ 0)
    (hi : Even i) : Nonempty (M.H i ≃+ Herbrand.TateZerothCohomology M.rho g₀) := by
  let _ : CommGroup G := commGroupOfZpowers g₀ hg
  obtain ⟨e⟩ := Herbrand.nonempty_groupCohomology_even M.rho g₀ hg i h0 hi
  exact ⟨(finEquiv M i).toAddEquiv.trans e⟩

theorem herbrand_layer (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] [Fintype (GalLK p K L)] (g₀ : GalLK p K L) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) :
    Herbrand.HFin (layer p K L).rho g₀ ∧ Herbrand.h (layer p K L).rho g₀ = degLK p K L := by
  have he : 0 < eK p L := eK_pos p L hL
  obtain ⟨hU, hU1⟩ := herbrand_layerU hK hL h g₀ hg
  obtain ⟨hZ, -, -, hZ1⟩ := Herbrand.h_int (trivRep (GalLK p K L) ℤ).rho (fun _ _ => rfl) g₀
  let v : (layer p K L).V →+ ℤ := (vOn p L).comp
    { toFun := fun x => ⟨x.1, layer_val_mem h x⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hv (x : (layer p K L).V) : (v x : ℝ) = eK p L * vbar p x.1 := vOn_spec p L _
  have hv_surjective : Surjective v := by
    intro n
    obtain ⟨x, hx⟩ := vOn_surjective_of_pos p L he n
    refine ⟨toLayer p x, Int.cast_injective (α := ℝ) ?_⟩
    exact (hv _).trans ((vOn_spec p L x).symm.trans (congrArg (fun a : ℤ => (a : ℝ)) hx))
  obtain ⟨h1, h2⟩ := Herbrand.h_mul (layerU p K L).rho (layer p K L).rho (trivRep (GalLK p K L) ℤ).rho g₀
    (layerUIncl p K L).u.toAddMonoidHom v (layerUIncl_injective p)
    (fun x => by
      change v x = 0 ↔ x ∈ Set.range (layerUIncl p K L).u.toAddMonoidHom
      have he' : (eK p L : ℝ) ≠ 0 := by positivity
      rw [← Int.cast_inj (α := ℝ), hv, Int.cast_zero, mul_eq_zero, or_iff_right he']
      constructor
      · intro hx
        exact ⟨⟨⟨x.1, hx⟩, fun g => Subtype.ext (x.2 g)⟩, Subtype.ext rfl⟩
      · rintro ⟨y, rfl⟩
        exact y.1.2)
    hv_surjective (fun c a => (layerUIncl p K L).equiv c a)
    (fun c x => by
      change v ((layer p K L).rho c x) = v x
      apply Int.cast_injective (α := ℝ)
      rw [hv, hv]
      induction c using QuotientGroup.induction_on with
      | H σ => exact congrArg (fun t : ℝ => (eK p L : ℝ) * t) (vbar_kbarRep p K σ x.1)) hU hZ
  refine ⟨h1, ?_⟩
  rw [h2, hU1, one_mul]
  exact hZ1

theorem subsingleton_h1_cyclic_layer (h : K ≤ L) [(subG p K L).Normal] [Fintype (GalLK p K L)] (g₀ : GalLK p K L)
    (hg : ∀ g, g ∈ Subgroup.zpowers g₀) : Subsingleton (Herbrand.H1 (layer p K L).rho g₀) := by
  have h1 : Subsingleton ((layer p K L).H 1) :=
    quotient_multiplicative_h1_subsingleton p K (subG p K L) (layer p K L) (layerInf p K L)
      (InflationRestrictionInvariants.invariants_isInvRep (kbarT p K) (subG p K L))
  have hS := totallySeparatedSpace_GalLK p K L
  have hT2 : T2Space (GalLK p K L) := TotallySeparatedSpace.t2Space
  have hT : T1Space (GalLK p K L) := T2Space.t1Space
  have hF : Finite (GalLK p K L) := Finite.of_fintype _
  have hD : DiscreteTopology (GalLK p K L) := Finite.instDiscreteTopology
  obtain ⟨e⟩ := nonempty_H_odd (layer p K L) g₀ hg 1 odd_one
  exact e.symm.toEquiv.subsingleton

theorem card_H0hat_layer (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] [Fintype (GalLK p K L)] (g₀ : GalLK p K L) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) :
    Nat.card (Herbrand.TateZerothCohomology (layer p K L).rho g₀) = degLK p K L := by
  have := subsingleton_h1_cyclic_layer h g₀ hg
  have h1 := (herbrand_layer hK hL h g₀ hg).2
  rw [Herbrand.h_eq_card_H0hat] at h1
  exact_mod_cast h1

theorem card_h2_cyclic_layer (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    [(subG p K L).Normal] (g₀ : GalLK p K L) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) :
    Nat.card ((layer p K L).H 2) = degLK p K L := by
  have := finite_GalLK (K := K) hL
  have hD : DiscreteTopology (GalLK p K L) := discreteTopology_GalLK hL
  let _ : Fintype (GalLK p K L) := Fintype.ofFinite _
  obtain ⟨e⟩ := nonempty_H_even (layer p K L) g₀ hg 2 two_ne_zero even_two
  rw [Nat.card_congr e.toEquiv, card_H0hat_layer hK hL h g₀ hg]

end ReciprocityTheory.DiscreteGroups.LocalClassField

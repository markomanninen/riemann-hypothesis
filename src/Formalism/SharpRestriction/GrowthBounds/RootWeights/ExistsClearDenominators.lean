module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightProjectionDiagonalApplyEqSmul
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionExtremalFormula
public import Lemmata.GeneralBFactLeftAltForm.MQ

@[expose] public section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section lat
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]

theorem exists_clear_denominators_alt (M : Submodule O W) (y : W) (hy : y ∈ MQ (K := KK O) M) : ∃ a : O, a ≠ 0 ∧ a • y ∈ M := by
  apply Bl.general_b_fact_left_alt_form.goal1
  exact hy

def latticeInter (M : Submodule O W) (L : Submodule (KK O) W) : Submodule O L :=
  M.comap (L.subtype.restrictScalars O)

theorem latticeInter_isLattice (M : Submodule O W) (hfg : M.FG) (hMQ : MQ (K := KK O) M = ⊤) (L : Submodule (KK O) W) :
    Submodule.IsFullLattice (KK O) (latticeInter M L) := by
  refine { toIsLattice := Submodule.IsLattice.of_fg (KK O) ?_, span_eq_top := ?_ }
  · have hN : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hfg
    refine Submodule.fg_of_fg_map_injective (L.subtype.restrictScalars O) (fun x y h => Subtype.ext h) ?_
    refine (isNoetherian_submodule.1 hN) _ ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  · apply top_unique
    intro x _
    obtain ⟨a, ha, hax⟩ := exists_clear_denominators_alt M (x : W) (by rw [hMQ]; trivial)
    have ha' : algebraMap O (KK O) a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 ha
    have hx : a • x ∈ latticeInter M L := hax
    have hspan := (Submodule.span (KK O) (latticeInter M L : Set L)).smul_mem
      (algebraMap O (KK O) a)⁻¹ (Submodule.subset_span hx)
    rwa [← algebraMap_smul (KK O) a x, inv_smul_smul₀ ha'] at hspan
end lat

theorem lattice_adapted_basis_exists : LatticeAdaptedBasisExists := by
  intro O _ _ _ W _ _ _ _ _ M hfg hMQ L
  have := latticeInter_isLattice M hfg hMQ L
  have := Submodule.IsLattice.finite (KK O) (latticeInter M L)
  have := Submodule.IsLattice.free (KK O) (latticeInter M L)
  let bO := Module.finBasis O (latticeInter M L)
  refine ⟨_, bO.extendOfIsFullLattice (KK O), fun i => ?_, fun x hx i => ?_⟩
  · rw [Module.Basis.extendOfIsFullLattice_apply]
    exact (bO i).2
  · obtain ⟨c, hc⟩ : ∃ c : Fin _ → O, x = ∑ j, (algebraMap O (KK O) (c j)) • (bO.extendOfIsFullLattice (KK O)) j := by
      refine ⟨fun j => bO.repr ⟨x, hx⟩ j, ?_⟩
      have h2 := congrArg (fun z : latticeInter M L => (z : L)) (bO.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h2
      refine h2.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [Module.Basis.extendOfIsFullLattice_apply, algebraMap_smul]
    refine ⟨c i, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc, map_sum]
    simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end Formalism.MainNotions.G.GLWeightTheory

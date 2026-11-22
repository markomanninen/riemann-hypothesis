module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.TraceInnerPosOfOrthonormalPair
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ExistsSmallMemFractionalIdeal
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ProdNormEmbeddingsEqAbsNorm
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.PlaneMassBoundOfFacts
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeIndexAndWeightTheory

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.HermitianLatticesTheory

theorem second_orthogonal_vector_holds (K : Type) [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) : SecondOrthogonalVector K :=
  by
    classical
    intro V _ _ _ _ h L hs hL M hlat hint huni x hx hx0
    obtain ⟨e, he, hspan, hLe, ho⟩ := hL
    let b : Basis (Fin 2) K V := Basis.mk he (by rw [hspan])
    have hfull : Submodule.IsFullLattice K M := by
      refine { toIsLattice := hlat, span_eq_top := ?_ }
      apply Submodule.dualAnnihilator_eq_bot_iff.mp
      apply le_antisymm ?_ bot_le
      intro f hf
      let v : V := ∑ i : Fin 2, star (f (e i)) • e i
      have hpair : h v = f := by
        apply b.ext
        intro i
        fin_cases i <;> simp [v, LinearMap.map_smulₛₗ, starRingEnd_apply, ho, b, Basis.coe_mk]
      have hline (r : K) : r • v ∈ M := by
        rw [← huni]
        simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
        intro y hy
        have hy0 : h v y = 0 := by
          rw [hpair]
          exact (Submodule.mem_dualAnnihilator f).mp hf y (Submodule.subset_span hy)
        have hz : h y v = 0 := by simpa [hy0] using (hs.eq v y).symm
        simp [hz]
      have hv : v = 0 := by
        by_contra hv
        obtain ⟨i, hi⟩ : ∃ i, b.repr v i ≠ 0 := by
          by_contra hn
          push_neg at hn
          apply hv
          apply b.repr.injective
          ext i
          simp [hn i]
        let c := ((Finsupp.lapply i).comp b.repr.toLinearMap).restrictScalars (𝓞 K)
        have htop : M.map c = ⊤ := by
          rw [eq_top_iff]
          intro a _
          refine ⟨(a / b.repr v i) • v, hline _, ?_⟩
          simp [c, div_mul_cancel₀ _ hi]
        have : Module.Finite (𝓞 K) K := Module.finite_def.mpr (htop ▸ hlat.fg.map c)
        exact RingOfIntegers.not_isField K
          (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 K) K) (Field.toIsField K))
      rw [Submodule.mem_bot]
      simpa [hv] using hpair.symm
    exact exists_orthogonal_second_vector K hK V h L ⟨e, he, hspan, hLe, ho⟩ M hfull hint huni x hx hx0

theorem plane_class_count_holds (K : Type) [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) : PlaneClassCount K :=
  fun V _ _ _ _ h L hs hL s hreps B₁ B₂ hint hshort => class_count_plane_bound K hK V h L hs hL s hreps B₁ B₂ hint hshort

end Formalism.MainNotions.BridgeLemma₂

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem plane_mass_le_height_pow (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C : ℝ)
    (hC : 55 * max 1 (1 / Cl) ≤ C ^ 2) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) : UnitaryVolumeMass.Mass2At D large₂ C := by
  have hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := D.sp.cm.cmUnram
  have hfin := Formalism.MainNotions.StandardLattice.finrank_host D
  have hrd : rootDiscriminant D.host.E = D.host.rdE := rfl
  have h19 : 1 ≤ D.host.v := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h19, -⟩ := hH
    exact h19
  have hrd0 : 0 ≤ D.host.rdE := by
    have e : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
    rw [← e]; linarith
  refine plane_mass_bound_of_facts D large₂ C' Cl Cg cb Cu cT CT C _ (short_vector_every_place D.host.E hK)
    (second_orthogonal_vector_holds D.host.E hK) (plane_class_count_holds D.host.E hK) ?_ ?_ hC hH
  · rw [hrd]; positivity
  · rw [hrd, hfin]; push_cast; apply le_of_eq; ring

theorem plane_mass_bound_parameters (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ)
    (hC : 55 * max 1 (1 / Cl) ≤ C ^ 2) : UnitaryVolumeMass.stMass2 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C :=
  fun hH => plane_mass_le_height_pow D large₂ C' Cl Cg cb Cu cT CT C hC hH.1.1

section Family

variable {eps : ℝ} (Fm : FamP eps)

end Family

end Formalism.MainNotions.BridgeLemma₂

end

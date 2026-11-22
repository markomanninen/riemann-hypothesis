module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LocSplitType
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomLocFOfVdZero
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsIsomScale

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open NumberField Formalism.HermitianLattices.Ext.L3

theorem local_unimodular_holds : Formalism.MainNotions.BridgeRowsGenus.LocUnimod := by
  intro F E _ _ _ _ _ _ hc S L M hL hM p hp huL huM
  classical
  have full (N : Submodule (𝓞 E) S.V) (hN : Submodule.IsLattice E N)
      (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt S.hT p N) :
      Submodule.IsFullLattice E N := by
    let D := Formalism.HermitianLatticesTheory.dual S.hT N
    have hd : Submodule.span E (D : Set S.V) = ⊤ := by
      obtain ⟨T, hT⟩ := hN.fg
      subst N
      apply eq_top_iff.mpr
      intro x _
      obtain ⟨n, hn, hint⟩ :=
        exists_integral_multiples ℤ ℚ (L := E) (T.image fun y => S.hT y x)
      have hx : n • x ∈ Formalism.HermitianLatticesTheory.dual S.hT
          (Submodule.span (𝓞 E) (T : Set S.V)) := by
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          rw [map_zsmul]
          exact Submodule.mem_one.mpr ⟨⟨_, hint _ (Finset.mem_image_of_mem _ hy)⟩, rfl⟩
        | zero => simp
        | add y z _ _ hy hz =>
          rw [map_add, LinearMap.add_apply]
          exact Submodule.add_mem _ hy hz
        | smul c y _ hy =>
          obtain ⟨r, hr⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range c
          rw [← algebraMap_smul E c y, map_smulₛₗ S.hT (algebraMap (𝓞 E) E c) y,
            LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, ← hr, ← smul_eq_mul,
            algebraMap_smul]
          exact Submodule.smul_mem _ r hy
      refine (Submodule.smul_mem_iff _ (Int.cast_ne_zero.mpr hn : (n : E) ≠ 0)).mp ?_
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.subset_span hx
    have hle : D ≤ Formalism.HermitianLatticesTheory.loc (K := E) p N := by
      have h1 := Formalism.HermitianLatticesTheory.locDual_loc_dual_le S.hT p N
      rw [← Formalism.HermitianLatticesTheory.locDual_dualAt_loc S.hT
        (RingOfIntegers.coe_injective)
        (Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range) p N, hu] at h1
      exact (Formalism.HermitianLatticesTheory.locBasic_le_locS _ D).trans h1
    refine { toIsLattice := hN, span_eq_top := ?_ }
    apply eq_top_iff.mpr
    intro x _
    have hx : x ∈ Submodule.span E (D : Set S.V) := hd ▸ Submodule.mem_top
    apply (Submodule.span_le.mpr ?_) hx
    intro y hy
    obtain ⟨s, hs, hsy⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp (hle hy)
    have hs0 := WA.algebraMap_ne_zero_of_mem_hcompl hp.isPrime hs
    apply (Submodule.smul_mem_iff _ hs0).mp
    rw [algebraMap_smul]
    exact Submodule.subset_span hsy
  have hF : IsFixF E F := fun a => by rw [hc.fixed a, RingHom.mem_range, Set.mem_range]
  obtain ⟨π, hπ, -, -⟩ := U0.exists_isUnif hF hp
  have hnd : G4.NondegOn S.hT ⊤ := by
    intro ξ _ hξ0
    by_contra hcon
    push Not at hcon
    exact hξ0 (S.nondeg.2 ξ fun w => hcon w Submodule.mem_top)
  obtain ⟨g, hg, -, hgM⟩ := G4.sd_main' (WA.isHermSemilocal_locRing hc.cmUnram hp) hπ S.herm
    two_ne_zero _ ⊤ ⊤ _ _ 1 le_rfl hnd (U0.isSD_loc (full L hL huL) hp.isPrime huL) (U0.isSD_loc (full M hM huM) hp.isPrime huM)
    (one_mem _) (fun _ => ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩)
  exact ⟨g, hg, U0.gmap_eq_of_iff hgM⟩

end Formalism.L2.SG.Pf.Cnt

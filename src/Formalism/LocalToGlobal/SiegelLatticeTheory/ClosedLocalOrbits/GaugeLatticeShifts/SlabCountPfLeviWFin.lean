module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfLeviSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ReHermitianCombinationNonpos

@[expose] public section

noncomputable section

open scoped Classical ComplexConjugate
open NumberField

namespace Formalism.L2.SG.Pf.SlabCount

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word)

theorem xsp_le_usp : Xsp (lf D (X.Fu u')) ≤ Usp X u' := by
  show Submodule.span D.host.E (Set.range (X.Fu u').e) ≤ _
  rw [X.Fu_e]
  exact Submodule.span_mono (Set.subset_union_of_subset_left Set.subset_union_left _)

theorem wsp_le_orth : Wsp X u' ≤ orth (VS D) (Xsp (lf D (X.Fu u'))) :=
  Formalism.L2.SG.Pf.orth_anti (xsp_le_usp X u')

theorem piWL_of_mem {w : (VS D).V} (hw : w ∈ Wsp X u') : piWL X u' w = w := by
  have h0 : ∀ x ∈ Usp X u', (VS D).hT x w = 0 := Formalism.L2.SG.Pf.mem_orth_iff_bl.1 hw
  have he : ∀ a, (VS D).hT (X.eX a) w = 0 := fun a =>
    h0 _ (Submodule.subset_span (Or.inl (Or.inl ⟨a, rfl⟩)))
  have hf : ∀ a, (VS D).hT (X.fY a) w = 0 := fun a =>
    h0 _ (Submodule.subset_span (Or.inl (Or.inr ⟨a, rfl⟩)))
  have hz : (VS D).hT (X.zu u') w = 0 := h0 _ (Submodule.subset_span (Or.inr rfl))
  simp [piWL, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smulRight_apply, he, hf, hz]

theorem hW_symm : (hW X u').IsSymm :=
  ⟨fun x y => (VS D).herm.eq (x : (VS D).V) (y : (VS D).V)⟩

theorem lw_isLattice (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Submodule.IsLattice D.host.E Λ) :
    Submodule.IsLattice D.host.E (LW X u' Λ) := by
  refine ⟨?_, ?_⟩
  ·
    let N : Submodule (𝓞 D.host.E) (VS D).V :=
      (Λ ⊓ (orth (VS D) (Xsp (lf D (X.Fu u')))).restrictScalars (𝓞 D.host.E)).map
        ((piWL X u').restrictScalars (𝓞 D.host.E))
    have hN : N.FG := by
      refine Submodule.FG.map _ ?_
      have : IsNoetherian (𝓞 D.host.E) Λ := isNoetherian_of_fg_of_noetherian Λ hΛ.fg
      exact (isNoetherian_submodule.1 this) _ inf_le_left
    have hle : (LW X u' Λ).map ((Wsp X u').subtype.restrictScalars (𝓞 D.host.E)) ≤ N := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have : IsNoetherian (𝓞 D.host.E) N := isNoetherian_of_fg_of_noetherian N hN
    exact Submodule.fg_of_fg_map_injective ((Wsp X u').subtype.restrictScalars (𝓞 D.host.E)) Subtype.val_injective
      ((isNoetherian_submodule.1 this) _ hle)
  ·
    intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

theorem lw_isFullLattice (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hΛ : Submodule.IsFullLattice D.host.E Λ) :
    Submodule.IsFullLattice D.host.E (LW X u' Λ) := by
  refine { toIsLattice := lw_isLattice X u' Λ hΛ.toIsLattice, span_eq_top := ?_ }
  rw [eq_top_iff]
  intro a _
  have ha : (a : (VS D).V) ∈ Submodule.span D.host.E (Λ : Set (VS D).V) := by
    rw [hΛ.span_eq_top]
    exact Submodule.mem_top
  obtain ⟨y, hy, r, hya⟩ :=
    (IsLocalization.mem_span_iff (nonZeroDivisors (𝓞 D.host.E))).mp ha
  rw [Submodule.span_eq] at hy
  have hr : (r : 𝓞 D.host.E) • a ∈ LW X u' Λ := by
    change (r : 𝓞 D.host.E) • (a : (VS D).V) ∈
      (Λ ⊓ (orth (VS D) (Xsp (lf D (X.Fu u')))).restrictScalars (𝓞 D.host.E)).map
        ((piWL X u').restrictScalars (𝓞 D.host.E))
    refine ⟨(r : 𝓞 D.host.E) • (a : (VS D).V), ⟨?_, ?_⟩, ?_⟩
    · rw [← IsScalarTower.algebraMap_smul D.host.E (r : 𝓞 D.host.E), hya,
        smul_smul, IsLocalization.mk'_spec', map_one, one_smul]
      exact hy
    · rw [← IsScalarTower.algebraMap_smul D.host.E (r : 𝓞 D.host.E)]
      exact (orth (VS D) (Xsp (lf D (X.Fu u')))).smul_mem _ (wsp_le_orth X u' a.2)
    · rw [← IsScalarTower.algebraMap_smul D.host.E (r : 𝓞 D.host.E)]
      exact piWL_of_mem X u' ((Wsp X u').smul_mem _ a.2)
  have hmul := Submodule.smul_mem (Submodule.span D.host.E (LW X u' Λ : Set (Wsp X u')))
    (IsLocalization.mk' D.host.E 1 r) (Submodule.subset_span hr)
  rwa [← IsScalarTower.algebraMap_smul D.host.E (r : 𝓞 D.host.E), smul_smul,
    IsLocalization.mk'_spec, map_one, one_smul] at hmul

theorem leviWFinC_of (hP : LeviPosC) : LeviWFinC := by
  intro D X Y u' Λ hΛ
  have hlat : Submodule.IsFullLattice D.host.E Λ := (((Y.rowsOK u').1 Λ hΛ).1).1
  refine Formalism.HermitianLatticesTheory.autFinite D.host.E (Wsp X u') (hW X u') (hW_symm X u') ?_ (LW X u' Λ)
    (lw_isFullLattice X u' Λ hlat)
  intro x hx
  exact hP D X u' x x.2 (fun h => hx (Subtype.ext h))

end Formalism.L2.SG.Pf.SlabCount

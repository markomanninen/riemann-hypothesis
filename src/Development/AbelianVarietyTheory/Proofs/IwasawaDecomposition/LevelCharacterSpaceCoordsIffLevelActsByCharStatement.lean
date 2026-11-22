module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterSpaceCoordsIffLevelActsByChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AvgLevel

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacterSpace_coords_iff_level_acts_by_char : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : CSD K) (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms) (P : Subgroup G) (ψ : P →* Kˣ) (f : S.Forms), (∃ x, S.basis.equivFun.symm ((S.lvlE r P ψ).mulVec x) = f) ↔ ∀ h : P, r h f = ((ψ h : Kˣ) : K) • f := by
  intro K _ _ _ S G _ _ r P ψ f
  constructor
  · rintro ⟨x, rfl⟩ p
    have h1 : (S.lvlE r P ψ).mulVec x ∈ LinearMap.range (imE (S.gaMat r (lvlIdem P ψ))).mulVecLin := ⟨x, rfl⟩
    rw [(image_idempotent_spec K S.dim (S.gaMat r (lvlIdem P ψ))).2, level_part_spec K S G r P ψ] at h1
    have hz := h1 p
    have h4 := S.I_actMat r (p : G) ((S.lvlE r P ψ).mulVec x)
    rw [hz, map_smul, CSD.I_apply] at h4
    apply Subtype.ext
    rw [← h4]
    rfl
  · intro hf
    have hI : Function.Injective S.I := by
      intro a b h
      rw [CSD.I_apply, CSD.I_apply] at h
      exact S.basis.equivFun.symm.injective (Subtype.ext h)
    have hzf : S.basis.equivFun.symm (S.basis.equivFun f) = f := S.basis.equivFun.symm_apply_apply f
    have hz : ∀ p : P, (S.actMat r (p : G)).mulVec (S.basis.equivFun f) =
        ((ψ p : Kˣ) : K) • S.basis.equivFun f := by
      intro p
      apply hI
      rw [S.I_actMat r (p : G) _, map_smul, CSD.I_apply, hzf, hf p]
      rfl
    have h1 : S.basis.equivFun f ∈ LinearMap.range (imE (S.gaMat r (lvlIdem P ψ))).mulVecLin := by
      rw [(image_idempotent_spec K S.dim (S.gaMat r (lvlIdem P ψ))).2, level_part_spec K S G r P ψ]
      exact hz
    obtain ⟨x, hx⟩ := h1
    refine ⟨x, ?_⟩
    have hx' : (S.lvlE r P ψ).mulVec x = S.basis.equivFun f := hx
    rw [hx', hzf]

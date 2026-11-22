module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemH0sub
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrincipleStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalAutomorphismLocalExtensionMovesLatticesStatement

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold

theorem gmap_isLattice_rat {D : D7} (g : GV D) (Λ : LV D) (hΛ : Submodule.IsLattice D.host.E Λ) :
    Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g Λ) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  exact Submodule.IsLattice.of_fg D.host.E (hΛ.fg.map _)

theorem gmap_isFullLattice_rat {D : D7} (g : GV D) (Λ : LV D)
    (hΛ : Submodule.IsFullLattice D.host.E Λ) :
    Submodule.IsFullLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g Λ) := by
  refine { toIsLattice := gmap_isLattice_rat g Λ hΛ.toIsLattice, span_eq_top := ?_ }
  change Submodule.span D.host.E (g.toLinearMap '' (Λ : Set (VS D).V)) = ⊤
  rw [Submodule.span_image, hΛ.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

theorem ext_fix_lattice_ae : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∀ h : ↥(FlagPairStabilizer F F'), {p | ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite := by
  intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ Λ₀ hΛ₀ h
  obtain ⟨-, -, hlat, -⟩ := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hR
  have hfin := ((GlobalTheory.T.hermitianLattice_local_global_principle D Z).1 (Formalism.HermitianLatticesTheory.gmap (h : GV D) Λ₀) Λ₀ (gmap_isFullLattice_rat _ _ hΛ₀) hΛ₀).1
  refine hfin.subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  intro heq
  apply hp
  apply Subgroup.subset_closure
  show LocNG.img _ _ = _
  rw [← hlat (h : GV D) p _ Λ₀ (hφ h p)]
  exact heq

end GlobalTheory.Unfold

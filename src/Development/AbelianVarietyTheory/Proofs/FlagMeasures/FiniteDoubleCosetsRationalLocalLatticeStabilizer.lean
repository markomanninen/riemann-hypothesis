module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemH0sub
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrincipleStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalLatticeClassesFiniteLocalOrbitsStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalAutomorphismLocalExtensionMovesLatticesStatement

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblCos

variable {D : D7}

theorem img_mul (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (a b : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (Λ : Submodule (M p).L.O (Vp D p)) :
    LocNG.img (a * b) Λ = LocNG.img a (LocNG.img b Λ) := by
  ext x
  simp only [LocNG.img, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    LinearEquiv.mul_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨b y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem img_one (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (Λ : Submodule (M p).L.O (Vp D p)) : LocNG.img (1 : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) Λ = Λ := by
  ext x
  simp [LocNG.img]

theorem mem_Aut_iff (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (Λ : Submodule (M p).L.O (Vp D p)) :
    g ∈ LocNG.Aut Λ ↔ LocNG.img g Λ = Λ := by
  constructor
  · intro hg

    let K : Subgroup (Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) :=
      { carrier := {a | LocNG.img a Λ = Λ}
        mul_mem' := fun {a b} ha hb => by
          have ha' : LocNG.img a Λ = Λ := ha
          have hb' : LocNG.img b Λ = Λ := hb
          show LocNG.img (a * b) Λ = Λ
          rw [img_mul p M, hb', ha']
        one_mem' := img_one p M Λ
        inv_mem' := fun {a} ha => by
          have ha' : LocNG.img a Λ = Λ := ha
          show LocNG.img a⁻¹ Λ = Λ
          calc LocNG.img a⁻¹ Λ = LocNG.img a⁻¹ (LocNG.img a Λ) := by rw [ha']
            _ = Λ := by rw [← img_mul p M, inv_mul_cancel, img_one p M] }
    exact (Subgroup.closure_le K).2 (fun a ha => ha) hg
  · intro h
    exact Subgroup.subset_closure h

theorem span_img (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (Λ : Submodule (M p).L.O (Vp D p))
    (h : Submodule.span (D.s.atP p).Ep (Λ : Set (Vp D p)) = ⊤) :
    Submodule.span (D.s.atP p).Ep (LocNG.img g Λ : Set (Vp D p)) = ⊤ := by
  have himg : (LocNG.img g Λ : Set (Vp D p)) = (g : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p) '' (Λ : Set (Vp D p)) := by
    ext x
    simp [LocNG.img]
  rw [himg, Submodule.span_image, h, Submodule.map_top]
  exact LinearEquiv.range g

theorem img_key (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (c g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (A B C : Submodule (M p).L.O (Vp D p))
    (h1 : C = LocNG.img c B) (h2 : C = LocNG.img g A) : LocNG.img (c⁻¹ * g) A = B := by
  rw [img_mul p M, ← h2, h1, ← img_mul p M, inv_mul_cancel, img_one p M]

theorem img_key' (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (c s g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (A B C : Submodule (M p).L.O (Vp D p))
    (h1 : C = LocNG.img c B) (h2 : C = LocNG.img g A) (h3 : LocNG.img s A = B) :
    LocNG.img ((c * s)⁻¹ * g) A = A := by
  rw [mul_inv_rev, mul_assoc, img_mul p M, img_key p M c g A B C h1 h2, ← h3, ← img_mul p M,
    inv_mul_cancel, img_one p M]

private theorem latP_fg_and_span_eq_top (Z : LocDat D) (Λ : LV D) (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (p : PlF D) :
    (lattice₂ D Z.M p Λ).FG ∧ Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
  haveI : Submodule.IsLattice D.host.E (GlobalTheory.Unfold.LatLoc.cL Λ) :=
    GlobalTheory.Unfold.LatLoc.isLattice_map (GlobalTheory.Unfold.LatLoc.cE D) Λ hΛ.toIsLattice
  have hc : Submodule.IsFullLattice D.host.E (GlobalTheory.Unfold.LatLoc.cL Λ) := by
    refine { span_eq_top := ?_ }
    change Submodule.span D.host.E ((GlobalTheory.Unfold.LatLoc.cE D).toLinearMap '' (Λ : Set (VS D).V)) = ⊤
    rw [← Submodule.map_span, hΛ.span_eq_top, Submodule.map_top, LinearEquiv.range]
  have h := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (GlobalTheory.Unfold.LatLoc.cL Λ) hc).2.1 p
  rw [GlobalTheory.Unfold.LatLoc.localLattice_eq]
  exact h

private theorem isFullLattice_of_local_span {D : D7} (Z : LocDat D) (p : PlF D) (Λ : LV D)
    (hΛ : Submodule.IsLattice D.host.E Λ)
    (hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤) :
    Submodule.IsFullLattice D.host.E Λ := by
  let U := Submodule.span D.host.E (Λ : Set (VS D).V)
  let b := Module.finBasis D.host.E U
  let W := Submodule.span (D.s.atP p).Ep
    (Set.range fun i => baseChange₂ D p (b i : (VS D).V))
  have hW (x : U) : baseChange₂ D p (x : (VS D).V) ∈ W := by
    have hx := congrArg (fun y : U => baseChange₂ D p (y : (VS D).V)) (b.sum_repr x)
    change baseChange₂ D p (U.subtype (∑ i, b.repr x i • b i)) = _ at hx
    rw [map_sum, map_sum] at hx
    rw [← hx]
    exact W.sum_mem fun i _ => by
      rw [map_smul, baseChange_smul₂]
      exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
  have htop : W = ⊤ := by
    apply top_le_iff.mp
    rw [← hspan, lattice₂, Submodule.span_span_of_tower]
    refine Submodule.span_le.2 ?_
    rintro y ⟨x, hx, heq⟩
    rw [← heq]
    exact hW ⟨x, Submodule.subset_span hx⟩
  refine { toIsLattice := hΛ, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
  rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
  simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
    finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)


private theorem gmap_inv_gmap_flag_measures (γ : GV D) (L : LV D) :
    Formalism.HermitianLatticesTheory.gmap γ⁻¹ (Formalism.HermitianLatticesTheory.gmap γ L) = L := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    have hz' : (γ⁻¹ : GV D) (γ z) = z := γ.symm_apply_apply z
    rw [hz']
    exact hz
  · intro hx
    refine ⟨γ x, ⟨x, hx, rfl⟩, ?_⟩
    exact γ.symm_apply_apply x

end GlobalTheory.DblCos


open GlobalTheory.DblCos in
set_option maxHeartbeats 5000000 in
theorem GlobalTheory.DblCos.finite_double_cosets : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∃ S : Finset (∀ p, ↥(FP p).UW0), (∀ s ∈ S, {p | ((s p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite) ∧ ∀ g : ∀ p, ↥(FP p).UW0, {p | ((g p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite → ∃ s ∈ S, ∃ h : ↥(FlagPairStabilizer F F'), ∃ k : ∀ p, ↥(FP p).UW0, (∀ p, ((k p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∈ LocNG.Aut (lattice₂ D Z.M p Λ₀)) ∧ g = φ h * s * k := by
  intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ Λ₀ hΛ₀
  obtain ⟨-, -, hLat, -⟩ := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hR
  obtain ⟨-, Slat, hSlat⟩ := GlobalTheory.T.rationalLatticeClasses_finite_localOrbits D X Y u u' F F' w hw hG Z FP hB hR Λ₀ hΛ₀
  obtain ⟨hcmp, hglue⟩ := GlobalTheory.T.hermitianLattice_local_global_principle D Z

  let fam : LV D → ∀ p, ↥(FP p).UW0 := fun Λs p =>
    if hc : (∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λs) ∧
        lattice₂ D Z.M p Λs ≠ lattice₂ D Z.M p Λ₀ then ⟨hc.1.choose, hc.1.choose_spec.1⟩ else 1
  have fam_one : ∀ Λs p, lattice₂ D Z.M p Λs = lattice₂ D Z.M p Λ₀ → fam Λs p = 1 := by
    intro Λs p he
    simp only [fam]
    rw [dite_eq_right]
    exact fun hc => hc.2 he
  have fam_spec : ∀ Λs p, (∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λs) →
      LocNG.img ((fam Λs p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (lattice₂ D Z.M p Λ₀) =
        lattice₂ D Z.M p Λs := by
    intro Λs p hex
    by_cases he : lattice₂ D Z.M p Λs = lattice₂ D Z.M p Λ₀
    · rw [fam_one Λs p he, he]
      exact img_one p Z.M _
    · have hc : (∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λs) ∧
          lattice₂ D Z.M p Λs ≠ lattice₂ D Z.M p Λ₀ := ⟨hex, he⟩
      simp only [fam, dif_pos hc]
      exact hc.1.choose_spec.2
  refine ⟨(Slat.filter (fun Λs => Submodule.IsFullLattice D.host.E Λs)).image fam, ?_, ?_⟩
  ·
    intro s hs
    obtain ⟨Λs, hmem, rfl⟩ := Finset.mem_image.1 hs
    have hL : Submodule.IsFullLattice D.host.E Λs := (Finset.mem_filter.1 hmem).2
    apply (hcmp Λs Λ₀ hL hΛ₀).1.subset
    intro p hp
    by_contra he
    apply hp
    rw [fam_one Λs p (not_not.1 he)]
    exact (mem_Aut_iff p Z.M _ _).2 (img_one p Z.M _)
  · intro g hg

    obtain ⟨Λ, hΛ, hΛp⟩ := hglue Λ₀ hΛ₀
      (fun p => LocNG.img ((g p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (lattice₂ D Z.M p Λ₀))
      (fun p => by
        obtain ⟨hfg, hspan⟩ := latP_fg_and_span_eq_top Z Λ₀ hΛ₀ p
        exact ⟨hfg.map _, span_img p Z.M _ _ hspan⟩)
      (by
        apply hg.subset
        intro p hp hmem
        exact hp ((mem_Aut_iff p Z.M _ _).1 hmem))
    obtain ⟨Λs, hΛsS, γ, hγ, hγΛ⟩ := hSlat Λ hΛ (fun p => ⟨_, (g p).2, (hΛp p).symm⟩)
    have hΛfull : Submodule.IsFullLattice D.host.E Λ := by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
      let p : PlF D := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField D.host.F)⟩
      apply isFullLattice_of_local_span Z p Λ hΛ
      rw [hΛp p]
      exact span_img p Z.M _ _ (latP_fg_and_span_eq_top Z Λ₀ hΛ₀ p).2
    have hΛsL : Submodule.IsFullLattice D.host.E Λs := by
      have hfull : Submodule.IsFullLattice D.host.E (Formalism.HermitianLatticesTheory.gmap γ⁻¹ Λ) := by
        refine { toIsLattice := GlobalTheory.RatLocMove.isLattice_gmap' γ⁻¹ Λ hΛ, span_eq_top := ?_ }
        change Submodule.span D.host.E (((γ⁻¹ : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V) '' (Λ : Set (VS D).V)) = ⊤
        rw [Submodule.span_image, hΛfull.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
        exact (γ⁻¹ : GV D).surjective
      rwa [← hγΛ, gmap_inv_gmap_flag_measures] at hfull
    let hh : ↥(FlagPairStabilizer F F') := ⟨γ, (mem_H0sub F F' γ).2 hγ⟩
    let s := fam Λs
    refine ⟨s, Finset.mem_image.2 ⟨Λs, Finset.mem_filter.2 ⟨hΛsS, hΛsL⟩, rfl⟩, hh,
      s⁻¹ * (φ hh)⁻¹ * g, ?_, by group⟩
    intro p

    have hC1 : lattice₂ D Z.M p Λ = LocNG.img ((φ hh p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)
        (lattice₂ D Z.M p Λs) := by
      rw [← hγΛ]
      exact hLat γ p _ Λs (hφ hh p)
    have hC2 := hΛp p
    have hex : ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λs :=
      ⟨(((φ hh p)⁻¹ * g p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p), ((φ hh p)⁻¹ * g p).2, by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, img_mul p Z.M, ← hC2, hC1, ← img_mul p Z.M,
          inv_mul_cancel, img_one p Z.M]⟩
    have hs := fam_spec Λs p hex
    rw [mem_Aut_iff p Z.M]
    have key := img_key' p Z.M _ _ _ _ _ _ hC1 hC2 hs
    simpa [Pi.mul_apply, Pi.inv_apply, mul_inv_rev, mul_assoc] using key

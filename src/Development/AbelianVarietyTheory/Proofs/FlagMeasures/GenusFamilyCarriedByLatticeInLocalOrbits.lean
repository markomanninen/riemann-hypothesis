module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLattices
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrinciple
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrincipleStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryComplementMovesLocalTermsWithDataStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermLatticeOverInnerDatumFgSpanStatement

@[expose] public section

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.GlueOrbit

variable {D : D7}

theorem finrank_loc (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  have h3 := D.R.m_add_three_le_k
  obtain ⟨c, hc⟩ := h1
  simp only [Ranks.r, Ranks.rS]
  omega

theorem localLattice_fg_and_span_eq_top (Z : LocDat D) (Λ : LV D) (h : Submodule.IsFullLattice D.host.E Λ) (p : PlF D) :
    (lattice₂ D Z.M p Λ).FG ∧ Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
  have hmap : Submodule.IsFullLattice D.host.E (LatLoc.cL Λ) := by
    refine { toIsLattice := LatLoc.isLattice_map _ _ h.toIsLattice, span_eq_top := ?_ }
    change Submodule.span D.host.E (((LatLoc.cE D).toLinearMap) '' (Λ : Set (VS D).V)) = ⊤
    rw [Submodule.span_image, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact (LatLoc.cE D).surjective
  have := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (LatLoc.cL Λ) hmap).2.1 p
  rw [LatLoc.localLattice_eq]
  exact this

theorem img_one {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (L : Submodule M.L.O V) :
    LocNG.img (1 : V ≃ₗ[E] V) L = L := by
  ext x
  simp [LocNG.img]

theorem img_lattice {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (g : V ≃ₗ[E] V) (L : Submodule M.L.O V)
    (h : L.FG ∧ Submodule.span E (L : Set V) = ⊤) :
    (LocNG.img g L).FG ∧ Submodule.span E (LocNG.img g L : Set V) = ⊤ := by
  refine ⟨h.1.map _, ?_⟩
  unfold LocNG.img
  rw [Submodule.map_coe]
  have e1 : (⇑((g : V →ₗ[E] V).restrictScalars M.L.O) : V → V) = ⇑(g : V →ₗ[E] V) := rfl
  rw [e1, Submodule.span_image, h.2, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

theorem glue_local_orbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y y' : Dat Z FP), LocOver Λ y → InGen y y' → ∃ Λ', LocOver Λ' y' ∧ ∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ' := by
  intro D X Y u u' F F' w _ _ Z FP _ hR Λ y y' ⟨hΛ, hτ⟩ ⟨hrel, hfin⟩
  have key : ∀ p, ∃ h ∈ (FP p).UW0, (y' p = y p → h = 1) ∧
      ∃ τ : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (y' p) τ ∧
        τ.abelian₂ = LocNG.img h (lattice₂ D Z.M p Λ) := by
    intro p
    obtain ⟨τ, hτ1, hτ2⟩ := hτ p
    by_cases hp : y' p = y p
    · exact ⟨1, one_mem _, fun _ => rfl, τ, hp ▸ hτ1, by rw [img_one, hτ2]⟩
    · obtain ⟨g, hg, hm⟩ := hrel p
      exact ⟨g, hg, fun h => absurd h hp, _,
        (GlobalTheory.T.unitaryComplement_moves_local_terms_with_data (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (finrank_loc p) (hR p) g hg
          (y p) (y' p) τ hτ1 hm).1, by rw [← hτ2]⟩
  choose h hU h1 τ hτ1 hτ2 using key
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
  let p : PlF D := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField D.host.F)⟩
  obtain ⟨t, ht, heq⟩ := hτ p
  have hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
    rw [← heq]
    exact (GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP p (y p) t ht).2
  have hfull : Submodule.IsFullLattice D.host.E Λ := by
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
  obtain ⟨Λ', hΛ', hp⟩ := (GlobalTheory.T.hermitianLattice_local_global_principle D Z).2 Λ hfull (fun p => LocNG.img (h p) (lattice₂ D Z.M p Λ))
    (fun p => by
      obtain ⟨t, ht, heq⟩ := hτ p
      apply img_lattice
      rw [← heq]
      exact GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP p (y p) t ht)
    (hfin.subset fun p hp hc => hp (by simp only [h1 p hc, img_one]))
  exact ⟨Λ', ⟨hΛ', fun p => ⟨τ p, hτ1 p, (hτ2 p).trans (hp p).symm⟩⟩, fun p => ⟨h p, hU p, (hp p).symm⟩⟩

end GlobalTheory.Unfold.GlueOrbit

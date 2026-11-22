module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrinciple
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermLatticeOverInnerDatumFgSpanStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResiduallyFiniteUnitOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemH0sub
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Unfold.GlueOver

theorem exists_locOver : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (d0 : Dat Z FP), (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ {p | ¬ ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ ∧ τ.abelian₂ = lattice₂ D Z.M p Λ₀}.Finite) → ∃ Λ : LV D, LocOver Λ d0 := by
  intro D Z FP d0 hT hΛ
  obtain ⟨Λ₀, hΛ₀, hfin⟩ := hΛ
  have hc : ∀ p, ∃ τ : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (d0 p) τ ∧
      ((∃ τ' : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (d0 p) τ' ∧ τ'.abelian₂ = lattice₂ D Z.M p Λ₀) →
        τ.abelian₂ = lattice₂ D Z.M p Λ₀) := by
    intro p
    by_cases h : ∃ τ' : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (d0 p) τ' ∧ τ'.abelian₂ = lattice₂ D Z.M p Λ₀
    · obtain ⟨τ', h1, h2⟩ := h
      exact ⟨τ', h1, fun _ => h2⟩
    · obtain ⟨τ', h1⟩ := hT p
      exact ⟨τ', h1, fun h' => absurd h' h⟩
  choose τ hτ hτ' using hc
  haveI : Infinite (PlF D) := GlobalTheory.LvT.Inh.ResFin.infinite_places D.host.F
  obtain ⟨p, hp⟩ := Infinite.exists_notMem_finset hfin.toFinset
  have hp' : ∃ t, LocNG.IsTermOver (FP p) (d0 p) t ∧ t.abelian₂ = lattice₂ D Z.M p Λ₀ := by
    by_contra h
    exact hp (hfin.mem_toFinset.mpr h)
  obtain ⟨t, ht, heq⟩ := hp'
  have hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ₀ : Set (Vp D p)) = ⊤ := by
    rw [← heq]
    exact (GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP p (d0 p) t ht).2
  have hfull : Submodule.IsFullLattice D.host.E Λ₀ := by
    let U := Submodule.span D.host.E (Λ₀ : Set (VS D).V)
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
    refine { toIsLattice := hΛ₀, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
    rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
    simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
      finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)
  obtain ⟨Λ, hΛ, heq⟩ := (GlobalTheory.Unfold.LatLoc.lattices_local_global D Z).2 Λ₀ hfull (fun p => (τ p).abelian₂)
    (fun p => GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP p (d0 p) (τ p) (hτ p))
    (hfin.subset (fun p hp h => hp (hτ' p h)))
  exact ⟨Λ, hΛ, fun p => ⟨τ p, hτ p, (heq p).symm⟩⟩

end GlobalTheory.Unfold.GlueOver

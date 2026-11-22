module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemH0sub
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsComplementUnitaryMulActionLocalInnerDatumStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusRestrictedProductStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameFixingIsometriesEmbedProdLocalUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalLatticeOverLocalInnerDataStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameFixingIsometryExtPreservesCompletionsAeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteDoubleCosetsRationalLocalLatticeStabilizerStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteRationalIsometriesFixingFramesConjStabilizStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalLatticeStabilisersCommensurableAlmostEverywStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMassEqSumOverRationalGroupOrbitsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermLatticeOverInnerDatumFgSpanStatement

@[expose] public section

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HL

namespace GlobalTheory.Unfold

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

theorem mass_genus_local_weights : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ d0 : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ {p | ¬ ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ ∧ τ.abelian₂ = lattice₂ D Z.M p Λ₀}.Finite) → ∃ V1 : ℝ, 0 < V1 ∧ ∀ d : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d p) τ) → {p | d p ≠ d0 p}.Finite → massA F F' d = ENNReal.ofReal (V1 * ∏ᶠ p, LocNG.Datum.wt (d0 p) (d p)) := by
  intro D X Y u u' F F' w hw hG Z FP hB hR d0 hd0 hΛ
  obtain ⟨φ, hφi, hφE⟩ := GlobalTheory.T.frameFixingIsometries_embed_prod_localUnitary D X Y u u' F F' w hw hG Z FP hB hR
  obtain ⟨Λ₀, hLO⟩ := GlobalTheory.T.exists_globalLattice_over_localInnerData D Z FP d0 hd0 hΛ
  have hrk : ∀ p : PlF D, Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
    intro p
    have hm : D.R.m = 2 * D.R.rS + 2 := by
      have := D.R.two_le_m; obtain ⟨a, ha⟩ := D.R.m_even; unfold Ranks.rS; omega
    rw [finrank_Vp]; unfold Ranks.r; omega
  have hact : ∀ p : PlF D, ∃ act : MulAction ↥(FP p).UW0 (LocNG.Datum (FP p)),
      (∀ (g : ↥(FP p).UW0) d d', LocNG.Datum.Moves g.1 d d' ↔ act.smul g d = d') ∧
      ∀ d (g : ↥(FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ act.smul g d = d :=
    fun p => GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (hrk p) (hR p)
  choose act hMv hSt using hact
  letI : ∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p)) := act
  have hMv' : ∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d' := hMv
  have hSt' : ∀ p (d : LocNG.Datum (FP p)) (g : ↥(FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ g • d = d := hSt
  obtain ⟨hc0, hfin, hdd⟩ := GlobalTheory.T.localLatticeStabilisers_commensurable_almostEverywhere D X Y u u' F F' w hw hG Z FP hB hR hMv' hSt' Λ₀ d0 hLO
  have hlat : Submodule.IsLattice D.host.E Λ₀ := hLO.1
  have hfull : Submodule.IsFullLattice D.host.E Λ₀ := by
    obtain ⟨p⟩ := GlobalTheory.PhiEmbed.exists_place D
    obtain ⟨τ, hτ, heq⟩ := hLO.2 p
    apply isFullLattice_of_local_span Z p Λ₀ hlat
    rw [← heq]
    exact (GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP p (d0 p) τ hτ).2
  obtain ⟨V1, hV1, hmain⟩ := GlobalTheory.T.mass_genus_restricted_product (fun p => ↥(FP p).UW0) (fun p => LocNG.Datum (FP p))
    (fun p => (LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype) ↥(FlagPairStabilizer F F') φ hφi
    (GlobalTheory.T.frameFixingIsometry_ext_preserves_completions_ae D X Y u u' F F' w hw hG Z FP hB hR φ hφE Λ₀ hfull)
    (GlobalTheory.T.finite_doubleCosets_rational_localLatticeStabilizers D X Y u u' F F' w hw hG Z FP hB hR φ hφE Λ₀
      (by first | exact hfull | exact hfull.toIsLattice))
    (GlobalTheory.T.finite_rationalIsometries_fixing_frames_conjStabilizer D X Y u u' F F' w hw hG Z FP hB hR φ hφE Λ₀ hfull) d0 hc0 hfin
  refine ⟨V1, hV1, fun d hd hfd => ?_⟩
  have h3 := hdd d hd
  rw [GlobalTheory.T.genusMass_eq_sum_over_rationalGroup_orbits D X Y u u' F F' w hw hG Z FP hB hR φ hφE hφi hMv' d]
  have hm2 := hmain d (fun p => ⟨(h3 p).1, (h3 p).2.1⟩) hfd
  have e : (∏ᶠ p, LocNG.Datum.wt (d0 p) (d p)) = ∏ᶠ p, invVol (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) (MulAction.stabilizer ↥(FP p).UW0 (d p)) := finprod_congr fun p => ((h3 p).2.2).symm
  refine hm2.trans ?_
  rw [e]

end GlobalTheory.Unfold

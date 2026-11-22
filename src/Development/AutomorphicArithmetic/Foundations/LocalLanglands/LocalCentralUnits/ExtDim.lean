module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionPreservesCuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionCentralCharacter
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.GoodSeg
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.WDBasic

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {r : IrrGL (k := w.adicCompletion E) → WD h}

private theorem charPol_seg (H : CuspT a ha r) (Δ : Segment (w.adicCompletion E)) (σ : Weil h) :
    (((r Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)).charPol σ
      = (Δ.ms.map fun y => (r y).charPol σ).prod := by
  have hspecial (x : WD h) (l : ℕ) :
      ((x.lpTw (((l : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) l)).charPol σ =
        ((Multiset.range l).map fun j : ℕ => (x.lpTw j).charPol σ).prod := by
    induction x using WD.ind with
    | hP n a =>
      have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
      rw [WD.lpSp, WD.lpTw_mk, WD.lpChar_mk, WD.charPol_mk, WDRep.tensor_ρ, WDRep.sp_ρ,
        GlobalTheory.WeilDeligne.SpCharpoly.charpoly_map_diagEnd]
      change _ = ∏ j ∈ Finset.range l, ((WD.mk a).lpTw (j : ℕ)).charPol σ
      rw [← Fin.prod_univ_eq_prod_range (fun j : ℕ => ((WD.mk a).lpTw (j : ℕ)).charPol σ)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, WDRep.tw_ρ, smul_smul, ← mul_zpow, WDRep.spEig,
        coe_qPow, ← Complex.cpow_add _ _ hq, ← Complex.ofReal_add, sub_add_cancel]
  rw [hspecial (r Δ.first) Δ.len, Segment.ms, Multiset.map_map]
  have h1 : ∀ j : Fin Δ.len, (r (Δ.term j)).charPol σ = ((r Δ.first).lpTw ((j : ℕ) : ℝ)).charPol σ := by
    intro j
    rw [Segment.term, show (((j : ℕ) : ℂ)) = ((((j : ℕ) : ℝ)) : ℂ) by push_cast; rfl, H.nu _ Δ.isCusp_first]
  change _ = ∏ j : Fin Δ.len, (fun y => (r y).charPol σ) (Δ.term j)
  simp only [h1]
  rw [Fin.prod_univ_eq_prod_range (fun j => ((r Δ.first).lpTw (j : ℝ)).charPol σ) Δ.len]
  rfl

private theorem dim_charPol {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : CuspT a ha r) (L : IsLExt r rc)
    (x : IrrGL (k := w.adicCompletion E)) :
    (rc x).lpDim = x.1 ∧ ∃ s, HasSupport x.rep s ∧ (∀ y ∈ s, y.IsCusp) ∧
      ∀ σ, (rc x).charPol σ = (s.map fun y => (r y).charPol σ).prod := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := Pr.exh (w.adicCompletion E) x
  have hs : HasSupport x.rep (msupp 𝔪) := GlobalTheory.LocGL.hasSupport_msupp_of_isL Pr.zel _ 𝔪 x hm
  have hcp : ∀ σ, (rc x).charPol σ = ((msupp 𝔪).map fun y => (r y).charPol σ).prod := by
    intro σ
    rw [L 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm), segSum, CuspExt.charPol_sumList, List.map_map,
      msupp, Multiset.map_bind, Multiset.prod_bind]
    have hl : ∀ (l : List (Segment (w.adicCompletion E))) (F : Segment (w.adicCompletion E) → ℂ[X]),
        (l.map F).prod = ((l : Multiset _).map F).prod := fun l F => by rw [Multiset.map_coe, Multiset.prod_coe]
    rw [hl, Multiset.coe_toList]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun Δ _ => charPol_seg H Δ σ)
  refine ⟨?_, msupp 𝔪, hs, fun y hy => hs.isCusp hy, hcp⟩
  rw [← WD.charPol_natDegree (rc x) 1, hcp, Polynomial.natDegree_multiset_prod_of_monic _
    (fun f hf => by obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hf; exact WD.charPol_monic _ _), Multiset.map_map]
  have h2 : ((msupp 𝔪).map ((fun p : ℂ[X] => p.natDegree) ∘ fun y => (r y).charPol 1)) = (msupp 𝔪).map Sigma.fst :=
    Multiset.map_congr rfl fun y hy => by
      simp only [Function.comp_apply, WD.charPol_natDegree]
      exact H.dim y (hs.isCusp hy)
  rw [h2, hs.sum_fst, Fintype.card_fin]

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.extDim :
    UpperTheory.Zero.LLC.ExtDim := by
  intro E Ω _ _ _ _ _ A w h a ha r rc H L x
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨hd, s, hs, hc, hcp⟩ := dim_charPol H L x
  refine ⟨⟨hd, s, hs, hc, hcp⟩, fun ω hω σ => ?_⟩
  obtain ⟨f, hf, hprod⟩ := GlobalTheory.T.centralCharacter_eq_prod_supercuspidalSupport Pr.bz (w.adicCompletion E) x s ω hs hω
  have he : ((rc x).eig σ).prod = (s.map fun y => ((r y).eig σ).prod).prod := by
    rw [WD.eig, hcp, prod_roots_prod_of_monic s (fun y => (r y).charPol σ) fun y => WD.charPol_monic _ _]
    rfl
  have hw : ((ω (a σ) : ℂˣ) : ℂ) = (s.map fun y => ((f y (a σ) : ℂˣ) : ℂ)).prod := by
    rw [hprod, ← Units.coeHom_apply, map_multiset_prod, Multiset.map_map]
    rfl
  constructor
  · have hn : ∀ m : Multiset ℂ, ‖m.prod‖ = (m.map fun z => ‖z‖).prod :=
      fun m => map_multiset_prod (normHom (α := ℂ)) m
    rw [he, hw, hn, hn, Multiset.map_map, Multiset.map_map]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun y hy => H.absCentral y (hc y hy) (f y) (hf y hy) σ)
  · rintro ⟨s', hs', hg⟩
    obtain rfl := (goodSeg (w.adicCompletion E)).2.2 x _ _ hs' hs
    rw [he, hw]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun y hy => H.central y (hc y hy) (hg y hy) (f y) (hf y hy) σ)

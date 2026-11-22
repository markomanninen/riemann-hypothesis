module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeRhamRankLubinTateLine
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical

open Module GlobalTheory.CompanionTheory.DeRhamChar GlobalTheory.CompanionTheory.LTRead in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem _root_.GlobalTheory.T.de_rham_rank_lubin_tate_line : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied6 l P AI) →
    ∀ (K LL : FinExt l), (∀ (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), μ x ∈ LL.1) →
    ∀ (χ : ↥(GK K) →* (↥K.1)ˣ), HasPeriods P K χ → ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1,
      Module.finrank ↥LL.1 ↥(DdR (P.PD K) (lineRep ((Units.map ((τ : ↥K.1 →+* ↥LL.1) : ↥K.1 →* ↥LL.1)).comp χ))) =
        Module.finrank ℚ_[l] ↥K.1 * 1 ∧
      ∀ (τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ),
        multV (P.PD K) (lineRep ((Units.map ((τ : ↥K.1 →+* ↥LL.1) : ↥K.1 →* ↥LL.1)).comp χ)) τ' a =
          if a = (if τ' = τ then (-1 : ℤ) else 0) then 1 else 0 := by
  rintro l _ P AI ⟨T⟩ K LL hsplit χ hP τ
  have := K.2
  have := LL.2
  set ψ : ↥(GK K) →* (↥LL.1)ˣ := (Units.map ((τ : ↥K.1 →+* ↥LL.1) : ↥K.1 →* ↥LL.1)).comp χ
  have hcomponent : ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ z ∈ DdRE (P.PD K) (lineRep ψ) τ',
      (∀ w ∈ DdRE (P.PD K) (lineRep ψ) τ', ∃ c : ↥LL.1, w = c • z) ∧
      z ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) (if τ' = τ then (-1 : ℤ) else 0) ∧
      z ∉ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) ((if τ' = τ then (-1 : ℤ) else 0) + 1) := by
    intro τ'
    obtain ⟨σ₀, h₀⟩ := exists_lift τ' K.1.val
    obtain ⟨y, hyact, h1, h2⟩ := hP (σ₀.comp τ)
    have hact : ∀ g : ↥(GK K), gc g σ₀ = σ₀ →
        P.actQdR (g : GQ l) y = algebraMap (Om l) P.R.BdR (σ₀ ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) * y :=
      fun g hg => hyact g.1 g.2 fun x => DFunLike.congr_fun hg (τ x)
    by_cases hτ : τ' = τ
    · have hμ : σ₀.comp τ = K.1.val := AlgHom.ext fun x => by
        rw [AlgHom.comp_apply, ← hτ]
        exact h₀ x
      obtain ⟨m1, m2⟩ := h1 hμ
      rw [ite_eq_left hτ]
      have m2' : y ∉ (P.PD K).Fil (1 + 1) := by
        rw [show (1 + 1 : ℤ) = 2 by norm_num]
        exact m2
      exact component_line P T ψ τ' σ₀ h₀ y hact 1 m1 m2'
    · have hμ : σ₀.comp τ ≠ K.1.val := fun h => hτ (AlgHom.ext fun x =>
        σ₀.toRingHom.injective ((h₀ x).trans (DFunLike.congr_fun h x).symm))
      obtain ⟨m1, m2⟩ := h2 hμ
      rw [ite_eq_right hτ]
      have m2' : y ∉ (P.PD K).Fil (0 + 1) := by
        rw [zero_add]
        exact m2
      have h3 := component_line P T ψ τ' σ₀ h₀ y hact 0 m1 m2'
      rw [neg_zero] at h3
      exact h3
  refine ⟨?_, fun τ' a => ?_⟩
  · have hc : Fintype.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 := by
      rw [← GlobalTheory.DeRhamSplit.card_emb K LL hsplit, Nat.card_eq_fintype_card]
    have := (GlobalTheory.Per.FontaineBound.ddR_finite_le (P.PD K)
      (PositivityTheory.LocInh.tied_field l P AI T).1 (lineRep ψ)).1
    obtain ⟨e1, -⟩ := GlobalTheory.DeRhamSplit.finrank_DdR (P.PD K) (lineRep ψ) hc 0
    have hone : ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Module.finrank ↥LL.1 ↥(DdRE (P.PD K) (lineRep ψ) τ') = 1 := by
      intro τ'
      obtain ⟨z, hz, hgen, -, h2⟩ := hcomponent τ'
      have hz0 : z ≠ 0 := fun h => h2 (h ▸ Submodule.zero_mem _)
      have hspan : DdRE (P.PD K) (lineRep ψ) τ' = ↥LL.1 ∙ z := by
        refine le_antisymm (fun w hw => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hz)
        obtain ⟨c, rfl⟩ := hgen w hw
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)
      rw [hspan]
      exact finrank_span_singleton hz0
    rw [e1, Finset.sum_congr rfl fun τ' _ => hone τ']
    simp [hc]
  · obtain ⟨z, hz, hgen, h1, h2⟩ := hcomponent τ'
    exact multV_of_gen (P.PD K) (lineRep ψ) τ' _ z hz hgen h1 h2 a

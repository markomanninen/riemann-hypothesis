module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorDualPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentConjugateToSquareStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorFinal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DoubledVacuumFunctionEigenOfSplitTransport
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplitParallelDerivativeLeftFixed

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
noncomputable section
namespace GlobalTheory.NabFixSplitV
open GlobalTheory.DblVacLineTransp GlobalTheory.DblVacLine GlobalTheory.SplitParLeft in
theorem connection_fixes_split_subspace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
      (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.W.J) (dbl (incM F G.V'.J)) dd (X.α / X.β) (diagCols (Fin a')) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ n ∈ GlobalTheory.InertDbl.NabD σ G.V' v, omd n (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  have hConj := GlobalTheory.T.adelicSchwartzSpace_le_span_pureTensors
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v hsp hT hψ h2 _ d' hd' dd omd hdc hws R hR0 hRv n hn
  set Φ := GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) with hΦdef
  have hLine : ∃ c : ℂ, omd n Φ = c • Φ := by
    obtain ⟨hSB, h0, θ, hθ, hvac⟩ := hTr.geo.hM'.vac v
    refine dbl_line_co hTr.base.std v hψ hTr.geo.hW.lat.toIsLattice hTr.geo.hV'.lat.toIsLattice ?_ d' (G.M'.vac v)
      ⟨hSB, h0, θ, hθ, ?_⟩ dd omd hdc hws.2.1 R hRv n hn.1
    · intro z hz
      have h := GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B _ _ G.V' G.W _ _ _ _
        hTr.base hTr.geo.hV' hTr.geo.hW v zᵀ ((at_transpose v z).2 hz)
      rw [mem_latAtV_transpose] at h
      rw [h]
      constructor
      · intro H γ hγ
        have := H γᵀ ((mem_latAtV_transpose _ _ v γ).2 hγ)
        rwa [symp_transpose] at this
      · intro H γ hγ
        have := H γᵀ ((mem_latAtV_transpose _ _ v γ).2 hγ)
        have e := symp_transpose (R := AF F) (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) z γᵀ
        rw [Matrix.transpose_transpose] at e
        rw [e]
        exact this
    · intro γ hγ
      have h := hvac γᵀ ((mem_latAtV_transpose _ _ v γ).2 hγ)
      have e : d'.rho B.ψ γ = G.M'.co.rho B.ψ γᵀ := by
        simp only [Darboux.rho]
        rw [← hd' γᵀ, Matrix.transpose_transpose]
      rw [e, ← symp_transpose (R := AF F) (cA σ) _ (incM F G.W.J) (incM F G.V'.J) γ γ]
      exact h
  obtain ⟨c, hc⟩ := hLine
  obtain ⟨s, hs, hsn⟩ := hConj F E σ B hTr.base a' G.V' v hsp h2 n hn
  have hs1 : omd s Φ = Φ := by
    let Ψ := tens (evFin F v) (G.M'.vac v) R
    have hΨ : Ψ ∈ schA F _ := hRv.2
    have hΦ : Φ ∈ schA F _ :=
      GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hΨ _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hΨ)
    obtain ⟨y, hy⟩ := Function.ne_iff.mp (hTr.geo.hM'.vac v).2.1
    have hΨne : Ψ ≠ 0 := by
      intro h0
      let x : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
      have hRx : R x = R 0 := by
        have := hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
        simpa using this
      have h1 := congrFun h0 x
      simp only [Ψ, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx, Pi.zero_apply] at h1
      exact mul_ne_zero hy hR0 h1
    obtain ⟨k, hk⟩ := dblFun_eigen_left hTr.base hTr.geo v hψ d' hd' dd omd hdc hws.2.1 R hRv s hs.1
    obtain ⟨l, hl, hinv, hl0⟩ := GlobalTheory.DblDiagForm.exists_form F _ Ψ hΨ hΨne
    obtain ⟨t, ht⟩ := hs.2
    have hS := hws.2.2 l hl (fun z φ hφ => hinv φ hφ _ _ (GlobalTheory.WeilM.SiegelModel.rho_diag B.ψ hdc z φ)) s t ht _ hΦ
    have hts := GlobalTheory.InertDbl.parD_diag_action F E σ G.V' v s hs t ht
    have hw : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w ∉ above E (X.T : Set (Pl F)) :=
      fun w h hm => hT (h ▸ hm)
    have ha : (X.α / X.β) (Matrix.GeneralLinearGroup.det t) = 1 := by
      rw [MonoidHom.div_apply,
        chr_det_eq_one G.V' hTr.geo.hV'.lat v X.α (fun w h => hTr.chars.unrα w (hw w h)) t hts.1 hts.2,
        chr_det_eq_one G.V' hTr.geo.hV'.lat v X.β (fun w h => hTr.chars.unrβ w (hw w h)) t hts.1 hts.2, div_one]
    have hb := GlobalTheory.IntegralDetModule.modu_norm_det G.V' hTr.geo.hV'.lat v t hts.1 hts.2
    rw [ha, hb] at hS
    simp only [Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_mul] at hS
    change omd s Φ = k • Φ at hk
    rw [hk, map_smul, smul_eq_mul] at hS
    have hk1 : k = 1 := (mul_eq_right₀ hl0).mp hS
    rw [hk, hk1, one_smul]
  have hs2 : omd s⁻¹ Φ = Φ := by
    conv_lhs => rw [← hs1]
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
  have e1 : omd (s * n * s⁻¹) Φ = c • Φ := by
    rw [map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp, hs2, hc, map_smul, hs1]
  have e2 : omd (n * n) Φ = (c * c) • Φ := by
    rw [map_mul, mul_apply_eq_comp, hc, map_smul, hc, smul_smul]
  rw [hsn, e2] at e1
  by_cases hΦ : Φ = 0
  · rw [hΦ, map_zero]
  have hcc : c * c = c := smul_left_injective ℂ hΦ e1
  have h01 : c = 0 ∨ c = 1 := by
    rcases mul_eq_zero.1 (show c * (c - 1) = 0 by linear_combination hcc) with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  rcases h01 with h0 | h1
  · exfalso
    apply hΦ
    have : omd n⁻¹ (omd n Φ) = Φ := by
      rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
    rw [← this, hc, h0, zero_smul, map_zero]
  · rw [hc, h1, one_smul]
end GlobalTheory.NabFixSplitV
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nabla_fixed_split_subspace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
      (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.W.J) (dbl (incM F G.V'.J)) dd (X.α / X.β) (diagCols (Fin a')) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ n ∈ GlobalTheory.InertDbl.NabD σ G.V' v, omd n (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  exact _root_.GlobalTheory.NabFixSplitV.connection_fixes_split_subspace
end

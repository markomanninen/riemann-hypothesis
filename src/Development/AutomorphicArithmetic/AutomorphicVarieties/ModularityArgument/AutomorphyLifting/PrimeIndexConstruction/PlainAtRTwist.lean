module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.MixSeedPAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DenseRangeUnitsR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.SphPlain

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.LocGL GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.LocLanglands Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open UpperTheory.V UpperTheory.V.Af
open Neutral.B1 GlobalTheory.HeckeGal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.Birth

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem plainTor_tw {x : IrrGL (k := k)} (h : GlobalTheory.RoadU.PlainTor x) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    GlobalTheory.RoadU.PlainTor (x.tw χ hχ) := by
  obtain ⟨s, hs, h1, hu⟩ := h
  refine ⟨s.map (·.tw χ hχ), (hs.tw χ hχ).of_equiv (x.twEquiv χ hχ), ?_, ?_⟩
  · intro y hy
    obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.1 hy
    exact h1 y' hy'
  · intro y hy z hz e
    obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨z', hz', rfl⟩ := Multiset.mem_map.1 hz
    rw [IrrGL.tw_nu] at e
    have hinv : IsSmoothChar χ⁻¹ := hχ.inv
    have e2 := congrArg (·.tw χ⁻¹ hinv) e
    simp only [IrrGL.tw_tw, mul_inv_cancel, IrrGL.tw_one] at e2
    exact hu y' hy' z' hz' e2

end Local

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

private theorem plainAtR_twist {π : TR.CuspSub F n} {v : HeightOneSpectrum (𝓞 F)} (h : PlainAtR π v) (χ : HChar F) :
    PlainAtR (π.twist χ) v := by
  intro σ hσ
  have e : (π.twist χ).twist χ⁻¹ = π := by
    rw [← TR.CuspSub.twist_mul, mul_inv_cancel, TR.CuspSub.twist_one]
  have h1 := hσ.twist χ⁻¹
  rw [e] at h1
  have h2 := h _ h1
  have hsm := GlobalTheory.HeckeComp.smooth_loc χ⁻¹ v
  have hsm' := GlobalTheory.HeckeComp.smooth_loc χ v
  have h3 : IrrGL.of (σ.twist (CuspSub.locDet n χ⁻¹ v) (TR.CuspSub.isOpen_ker_locDet χ⁻¹ v)).ρ
      (σ.twist (CuspSub.locDet n χ⁻¹ v) (TR.CuspSub.isOpen_ker_locDet χ⁻¹ v)).smooth
      (σ.twist (CuspSub.locDet n χ⁻¹ v) (TR.CuspSub.isOpen_ker_locDet χ⁻¹ v)).irred =
      (IrrGL.of σ.ρ σ.smooth σ.irred).tw (χ⁻¹.loc v) hsm :=
    (IrrGL.tw_of σ.ρ σ.smooth σ.irred _ hsm).symm
  rw [h3] at h2
  have h4 := plainTor_tw h2 (χ.loc v) hsm'
  rw [IrrGL.tw_tw] at h4
  have e3 : χ⁻¹.loc v * χ.loc v = 1 := MonoidHom.ext fun x => by
    change (χ.loc v x)⁻¹ * χ.loc v x = 1
    simp
  have key : ∀ (c : (v.adicCompletion F)ˣ →* ℂˣ) (hc : IsSmoothChar c), c = 1 →
      (IrrGL.of σ.ρ σ.smooth σ.irred).tw c hc = IrrGL.of σ.ρ σ.smooth σ.irred := by
    rintro _ hc rfl
    exact IrrGL.tw_one _ _
  rwa [key _ _ e3] at h4

end UpperTheory.V.Z.Win.Birth

theorem UpperTheory.V.Z.Win.Birth.prTw :
    UpperTheory.V.Z.Win.Birth.PrTw := by
  rintro F Ω _ _ _ _ _ _ l _ ι r κ ⟨-, art, χ, a, ha, hχ, hL⟩ ⟨π, hr, hA, hP⟩
  have expo_intR : ∀ v : InfinitePlace F, ∃ k : ℤ, TR.expo χ v = k := by
    let diagR : F →+* TR.Rinf F :=
      (TR.pInf F).comp (algebraMap F (Ad F))

    have infDiag_eqR (k : Fˣ) : infDiag k = TR.infId F (Units.map diagR.toMonoidHom k) := by
      classical
      have h : ((infDiag k : Ideles F) : AdeleRing (𝓞 F) F) = (algebraMap F (InfiniteAdeleRing F) k, 1) := by
        unfold infDiag
        rw [MonoidHom.finsetProd_apply, Units.coe_prod]
        let infIncl : (∀ w : InfinitePlace F, w.Completion) →* AdeleRing (𝓞 F) F :=
          MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
        change ∏ w : InfinitePlace F, infIncl (Pi.mulSingle w (algebraMap F w.Completion k)) =
          infIncl (fun w => algebraMap F w.Completion k)
        rw [← map_prod, Finset.univ_prod_mulSingle]
      apply Units.ext
      rw [h]
      refine Prod.ext ?_ ?_
      · change _ = 1 - TR.infEq F 1 + TR.infEq F ((TR.infEq F).symm (algebraMap F (InfiniteAdeleRing F) k))
        simp
      · change (1 : Af F) = 1 - 0 + 0
        simp

    have denseRange_diagR : DenseRange diagR := by
      have hc : Continuous (TR.infEq F).symm := continuous_pi fun w =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
          (continuous_apply w)
      exact (TR.infEq F).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap F) hc

    have denseRange_unitsR : DenseRange (Units.map diagR.toMonoidHom) := by
      refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ => ?_
      obtain ⟨k, v, hv, hk⟩ := denseRange_diagR.exists_mem_open (Units.isOpenEmbedding_val.isOpenMap U hU) ⟨_, u, hu, rfl⟩
      have h0 : k ≠ 0 := by
        rintro rfl
        exact v.ne_zero (hk.trans (map_zero _))
      exact ⟨v, hv, Units.mk0 k h0, Units.ext hk.symm⟩

    have diagR_mk (φ : F →+* ℂ) (k : F) : ((diagR k (InfinitePlace.mk φ) : ℝ) : ℂ) = φ k := by
      have hr := IsTotallyReal.isReal (InfinitePlace.mk φ)
      have e : diagR k (InfinitePlace.mk φ) = InfinitePlace.embedding_of_isReal hr k := by
        change InfinitePlace.Completion.extensionEmbeddingOfIsReal hr
          (algebraMap F (InfinitePlace.mk φ).Completion k) = _
        rw [AbsoluteValue.Completion.algebraMap_def]
        simp [WithAbs.algebraMap_right_apply]
      rw [e, InfinitePlace.embedding_of_isReal_apply,
        InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hr)]

    have chiInf_pos (u : (TR.Rinf F)ˣ)
        (hu : ∀ v, 0 < u.val v) :
        ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : F →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ a φ := by
      have hc : ∀ v, Continuous fun u : (TR.Rinf F)ˣ => u.val v := fun v => (continuous_apply v).comp Units.continuous_val
      have ho : IsOpen {u : (TR.Rinf F)ˣ | ∀ v, 0 < u.val v} := by
        rw [Set.ofPred_forall]
        exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (hc v)
      have hcl : IsClosed {u : (TR.Rinf F)ˣ |
          ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : F →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ a φ} :=
        isClosed_eq (Units.continuous_val.comp (TR.continuous_chiInf χ)) (continuous_finsetProd _ fun φ _ =>
          (Complex.continuous_ofReal.comp (hc _)).zpow₀ _ fun u => Or.inl
            (Complex.ofReal_ne_zero.2 (TR.unit_ne_zero u _)))
      refine closure_minimal ?_ hcl (denseRange_unitsR.open_subset_closure_inter ho hu)
      rintro _ ⟨hk, k, rfl⟩
      have h1 := hχ k fun φ => by
        have h2 := hk (InfinitePlace.mk (Complex.ofRealHom.comp φ))
        have h3 := diagR_mk (Complex.ofRealHom.comp φ) (k : F)
        exact h2.trans_eq (Complex.ofReal_injective h3)
      rw [HChar.inf, MonoidHom.comp_apply, infDiag_eqR] at h1
      refine h1.trans (Finset.prod_congr rfl fun φ _ => ?_)
      exact congrArg (· ^ a φ) (diagR_mk φ (k : F)).symm

    intro v
    classical
    refine ⟨∑ φ : F →+* ℂ, if InfinitePlace.mk φ = v then a φ else 0, TR.expo_eq_of_exp χ v _ fun t => ?_⟩
    rw [chiInf_pos _ fun w => Real.exp_pos _]
    simp only [TR.expU_val, Complex.ofReal_exp, ← Complex.exp_int_mul]
    rw [← Complex.exp_sum, Int.cast_sum, Finset.sum_mul]
    refine congrArg _ (Finset.sum_congr rfl fun φ _ => ?_)
    split_ifs with e
    · rw [e, Pi.single_eq_same]
    · simp [Pi.single_eq_of_ne e]

  have hAtt : AttR ι (tw r κ) (π.twist χ) := by
    have ev_notMem :
        ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ((l : ℕ) : 𝓞 F) ∉ v.asIdeal := by
      have hl : l.Prime := Fact.out
      have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
        rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
        exact_mod_cast hl.ne_zero
      refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun v hv => ?_)
      exact Ideal.dvd_span_singleton.mpr (not_not.1 hv)
    change AttachedSys ι r π.HasSat at hA
    refine ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ (G F Ω) _ 2 r).2.2 κ hA.1, ?_⟩
    filter_upwards [hA.2, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified χ), ev_notMem]
      with w ⟨B, hB, hE⟩ hu hl
    refine ⟨_, hB.twist hu, ?_⟩
    have hc : UpperTheory.V.Af.Bc.CharEig ι κ w (χ.val w : ℂ) := by
      refine fun A hOver => ⟨(hL.unr_iff ha (Or.inl hl) hOver).2 hu, fun σ hσ => ?_⟩
      rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inl hl) hu hOver hσ, inv_inv, RingEquiv.apply_symm_apply]
    have h4 := UpperTheory.frobenius_eigenvalues_twist F Ω l ι 2 r κ w _ _ hE hc
    convert h4 using 1
    simp only [algSat, Multiset.bind_singleton, Multiset.map_map, Multiset.pure_def, Multiset.bind_def]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Units.val_mul, mul_assoc]
  refine ⟨π.twist χ, hr.twist expo_intR, hAtt, fun v => ?_⟩
  rcases hP v with h | ⟨B, hB⟩
  · exact Or.inl (plainAtR_twist h χ)
  · by_cases hu : χ.UnrAt v
    · exact Or.inr ⟨_, hB.twist hu⟩
    · exact Or.inl (plainAtR_twist (plainAtR_of_hasSat (by norm_num) π v B hB) χ)

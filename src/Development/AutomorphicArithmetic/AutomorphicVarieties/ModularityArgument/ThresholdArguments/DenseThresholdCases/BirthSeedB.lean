module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.CuspidalRankFourRegularAlgebraicTotallyComplex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistInvarianceAutomorphic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWCsdOf

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Ws.Pt UpperTheory.V.Z.Win
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp Formalism.BasicNotions Formalism.MainNotions.N
namespace UpperTheory.V.Z.Win.Birth
theorem ptAutR'_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (n : ℕ) (ι : PadicAlgCl l ≃+* ℂ) (r : G T.F Ω →* M4 (PadicAlgCl l)), (∀ g, IsGSp (algebraMap c'.O (PadicAlgCl l) (inc h (D.th (resQ T.F g)))) (r g)) → ∀ (κ : G T.L Ω →* (PadicAlgCl l)ˣ) (π : CuspSub T.L 4) (a : ℤ) (k : ℕ), Continuous κ → 0 < k → Even (a + n) → (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := T.L) A, (κ s ^ 2 * cycBar T.L Ω l s ^ (-a)) ^ k = 1) → CuspidalRankFourRegularAlgebraicTotallyComplex π → Af.AttC ι (Af.tw (r.comp (resLe T.F_le)).toHomUnits κ) π → (∀ w : HeightOneSpectrum (𝓞 T.L), ((l : ℕ) : 𝓞 T.L) ∈ w.asIdeal → PotUnl (K.rhoQ n r) w) → IsAutCsdA ι (K.rhoQ n r) := by
  intro hP Ω _ _ _ l _ c D T c' h K n ι r hr κ π a k hκ hk ha hw ⟨hreg, hwin⟩ hatt hpot
  have h1 := (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hP T.L Ω l ι 4 _).2.1.2 ⟨π, hreg, hatt⟩
  have h2 : Af.IsAlgChar ι (K.twc n * κ⁻¹) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s hP T.L Ω l ι).1 _ ((twc_cont K n).mul hκ.inv) fun w hlw => ?_
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    have hl : A.valuation (l : Ω) < 1 := by
      have h1 := (hA ((l : ℕ) : 𝓞 T.L)).2 hlw
      have e : algebraMap T.L Ω (((l : ℕ) : 𝓞 T.L) : T.L) = (l : Ω) := by simp
      rwa [e] at h1
    obtain ⟨e, k', hk', he, H⟩ := twWts K n A hl
    obtain ⟨m, hm⟩ : Even (e - a) := by
      have := he.sub ha
      rwa [add_sub_add_right_eq_sub] at this
    have half_pow {M : Type} [CommGroup M] {x y u : M} {a e m : ℤ} {k k' : ℕ}
        (hm : e - a = m + m) (hx : (x ^ 2 * u ^ (-e)) ^ k' = 1)
        (hy : (y ^ 2 * u ^ (-a)) ^ k = 1) :
        (x * y⁻¹ * u ^ (-m)) ^ (2 * (k * k')) = 1 := by
      obtain rfl : e = a + m + m := by omega
      have hsq : (x * y⁻¹ * u ^ (-m)) ^ 2 =
          (x ^ 2 * u ^ (-(a + m + m))) * (y ^ 2 * u ^ (-a))⁻¹ := by
        rw [mul_inv, mul_mul_mul_comm, mul_pow, mul_pow, inv_pow]
        congr 1
        group
      have hx' : (x ^ 2 * u ^ (-(a + m + m))) ^ (k * k') = 1 := by
        rw [mul_comm k k', pow_mul, hx, one_pow]
      have hy' : (y ^ 2 * u ^ (-a)) ^ (k * k') = 1 := by
        rw [pow_mul, hy, one_pow]
      rw [pow_mul, hsq, mul_pow, inv_pow, hx', hy', inv_one, mul_one]
    exact ⟨A, hA, m, 2 * (k * k'), by positivity, fun s hs => half_pow hm (H s hs) (hw A hl s hs)⟩
  have h3 := _root_.UpperTheory.V.Af.twist_invariance_automorphic hP T.L Ω l ι 4 _ _ h1 h2
  have h4 : Af.tw (Af.tw (r.comp (resLe T.F_le)).toHomUnits κ) (K.twc n * κ⁻¹) = K.rhoQ n r := by
    ext g : 2
    rw [Af.tw_val, Af.tw_val, smul_smul, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul,
      Units.inv_mul_cancel_right, K.rho_val]
    rfl
  rw [h4] at h3
  obtain ⟨P, hPair⟩ := ptPair K n r hr
  haveI : IsAlgClosure T.L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  have h5 : Sd.IsAlgChar ι (K.twc n * κ⁻¹) := by
    obtain ⟨χ, hc, art, a', b1, b2, b3⟩ := h2
    exact ⟨hc, art, χ, a', b1, b2, b3⟩
  have h6 := awTw T.L Ω l 4 (by norm_num) ι _ _ h5 ⟨π, hreg, hatt⟩ (awOne T.L Ω l 4 (by norm_num) ι _ π hatt hwin)
  rw [h4] at h6
  exact ⟨_root_.UpperTheory.GalN.V.csdOf0_alt hP (W.Lp T.L) T.L Ω inferInstance l ι 4 (by norm_num) _ K.s.c P K.s.hc h3 hPair, fun _ => h6.witA hpot⟩
end UpperTheory.V.Z.Win.Birth
end

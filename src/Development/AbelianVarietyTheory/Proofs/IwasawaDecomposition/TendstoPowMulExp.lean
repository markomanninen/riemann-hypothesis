module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentRulBC
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteDimensionalOfLeHolSub
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspPnormLeExpNegOfIsIsoStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameOrbitLiftOfArcStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameOrbitUnipotentOrderTwoStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrivialMonodromyOrbitConvergesSymmetricDomainStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryArcLiftNotConvergesSymmetricDomainStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameOrbitIsotropicVectorShortStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcLiftPeriodsTendstoSpanStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFrameLimitsOfOrbit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnKeySectionComplexValue
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnNaturalRuleHolomorphicFrames
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnReadingsNormalisedThetaPoints
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsChartHolomorphicCoordinatesNearFrameStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnExponentialFrameMatrixStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnThetaAlgebraicGeneratorFactorStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsThetaPtStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsFrameRatioStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsChangeLevelIsometryLinearMapStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointTriangularFrameWeightRule
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionary
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TriangularFrameMovesPeriodBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NonemptyThetaDataFlagDomainModels
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOfImHermFormEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedPointsSatisfySingleFrame
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFrameFrames
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousOnHolomorphicFramedFamily
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChangeStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOneStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOneStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorIsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bridge
public import ReciprocityTheory.SemistableReduction.ShareDetA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeromorphicGermVanishesOfPeriodicExpModulusStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionInvariantFrameFunction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEquationHolomorphicLimit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramePointEigenframe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChange

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem tendsto_pow_mul_exp (C C' c c' T : ℝ) (B : ℕ) (hc : 0 < c) (hc' : 0 < c') :
    Tendsto (fun w : ℂ => C * Real.exp (-c * (c' * (w.im - T))) * (C' * w.im ^ B)) imTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t ^ B * Real.exp (-(c * c') * t)) atTop (𝓝 0) := by
    have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (B : ℝ) (c * c') (mul_pos hc hc')
    simpa only [Real.rpow_natCast] using this
  have h2 := (h1.const_mul (C * C' * Real.exp (c * c' * T))).comp (tendsto_comap (f := Complex.im))
  rw [mul_zero] at h2
  refine h2.congr fun w => ?_
  have : Real.exp (-c * (c' * (w.im - T))) = Real.exp (c * c' * T) * Real.exp (-(c * c') * w.im) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [Function.comp, this]
  ring

theorem tendsto_cusp {N : ℕ} {X : Data E N} {T : ℝ} {x : ℂ → Frame X.Ψ N} {la : Wt X.Ψ N} {P : Frame X.Ψ N → ℂ}
    (hP : P ∈ X.SS la) (hd : ∀ w : ℂ, T < w.im → x w ∈ X.dom) {ξ : Fin N → E} {c' : ℝ} (hξ : X.IsIso ξ) (hc' : 0 < c')
    (ht : ∀ w : ℂ, T + 1 < w.im → ∀ τ, c' * (w.im - T) ≤ X.tt ξ (x w) τ) {C' : ℝ} {B : ℕ}
    (hn : ∀ᶠ w in imTop, 0 < X.nfac la (x w) ∧ (X.nfac la (x w))⁻¹ ≤ C' * w.im ^ B) :
    Tendsto (fun w => P (x w)) imTop (𝓝 0) := by
  obtain ⟨C, c, hc, hC⟩ := GlobalTheory.T.pnorm_le_exp_neg_of_mem_SS_of_isIso E N X la P ξ hP hξ
  refine squeeze_zero_norm' ?_ (tendsto_pow_mul_exp C C' c c' T B hc hc')
  have he : ∀ᶠ w in imTop, T + 1 + 1 / c' < w.im :=
    (tendsto_comap (f := Complex.im)).eventually (eventually_gt_atTop _)
  filter_upwards [hn, he] with w h1 h2
  have h0 : 0 < 1 / c' := by positivity
  have h3 : 1 ≤ c' * (w.im - T) := by
    have : 1 / c' ≤ w.im - T := by linarith
    rwa [div_le_iff₀' hc'] at this
  have h4 := hC (x w) (hd w (by linarith)) _ h3 (ht w (by linarith))
  have h5 : ‖P (x w)‖ = X.pnorm la P (x w) * (X.nfac la (x w))⁻¹ := by
    show _ = ‖P (x w)‖ * X.nfac la (x w) * _
    rw [mul_assoc, mul_inv_cancel₀ h1.1.ne', mul_one]
  have h6 : 0 ≤ X.pnorm la P (x w) := mul_nonneg (norm_nonneg _) h1.1.le
  rw [h5]
  exact mul_le_mul h4 h1.2 (inv_nonneg.2 h1.1.le) (h6.trans h4)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type}
  [CommRing O] {β : O →+* c.F}

end GlobalTheory.ShFam.BdArc

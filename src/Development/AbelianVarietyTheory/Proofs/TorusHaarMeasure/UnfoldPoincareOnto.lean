module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustGPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradFPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneLeMinorOfIsOrth
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MulSgnMatMulConjTranspose
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsUpqSubmatrix
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsLeNormDev
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormFderivLeOfClosedBallSubset
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.KaFrameOfDelta
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.KaUnfoldOfUnfoldOfKappa
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DminCptEq
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PairUnfoldOfUnfold
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PoinStatementOf
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PoinSummableIsBddSec
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OfRealTsumSqLeTsumDivMulTsum
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralLeDensity
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormLeSqrtWeightNearOrthonormal
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetSatFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IntegralEqIntegralTsumOfLintegral

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory.PoincareClosed

theorem unfold_poincare_onto :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ ψ : Frame X.Ψ r → ℝ≥0∞, Measurable ψ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) → ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 = ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0) ∧ (KaUnfoldStatement (E := E)) ∧ (PairUnfoldStatement (E := E)) ∧ (PoinStatement (E := E)) ∧ (OntoStatement (E := E)) := by
  obtain ⟨-, hMeas, -, hExt⟩ := GlobalTheory.FrameMeasureClosed.measure_statements (E := E)
  have hUnf := GlobalTheory.Unfold.lintegral_unfold (E := E) hMeas
  have hκ := GlobalTheory.kaFrame (E := E) GlobalTheory.FramePotential.frame_potential_basic
    GlobalTheory.MinorRatioNear.minorRatio_near (GlobalTheory.FrameSumBound.frame_sum_bound GlobalTheory.grpSep)
  have hKa : KaUnfoldStatement (E := E) := GlobalTheory.kaUnfold_of_unfold_of_kappa hUnf hκ
  have hPair : PairUnfoldStatement (E := E) :=
    GlobalTheory.PairUnfold.pairUnfold_of_unfold (GlobalTheory.UnfoldComplex.unfold_integral hUnf) hKa
  have hN := GlobalTheory.NormFactor.nfac_transform (E := E)
  have hPoin : PoinStatement (E := E) :=
    GlobalTheory.PoincareAssembly.poinStatement_of hκ
      (GlobalTheory.PointSup.pointSup hMeas GlobalTheory.OrthNear.orthNear hN)
      (GlobalTheory.norm_le_sqrt_weight_near_orthonormal hMeas GlobalTheory.OrthNear.orthNear hN)
      (GlobalTheory.PoinHol.poin_summable_isBddSec GlobalTheory.differentiableOn_tsum_of_norm_le hN)
      (GlobalTheory.poincare_sqIntegrable_fundSet hUnf)
  exact ⟨hUnf, hKa, hPair, hPoin,
    onto_of hPoin hExt RhGradFStatement_holds exhaustG_holds hKa hPair bigCellStatement_holds
      OmFConnStatement_holds⟩

end GlobalTheory.PoincareClosed

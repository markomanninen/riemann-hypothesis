module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FamilyStatementOfAbsAndVandermonde
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.GammaRangeOfSizeHypotheses
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumNormSqOrthonormalLeHilbertSchmidt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagAtScale
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DiagCLC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ExpQuarterMulExpQuarterLeTwo
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.AutomorphicFormsFiniteUnitaryIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Formalism.PeriodIntegrals.BesselMapUniq
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNml
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataChoiceLeaves
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
public import Formalism.LocalRingCardinality.DataTies
public import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedUniformRotatedOfExpansion
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThmBChain
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypOfUniqGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMultiplicityOneLargeGapAndWhittakerBessel
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneBesselTorusTranslatesLargeGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPointwiseBoundAtLargeGaps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqBesselFunctionLargeGaps
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesCoefPointwiseBoundUnconditional
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ElementarySizeBoundsOfSizeHypotheses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormSqLeadMinorTurnP
public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceExpansion
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.StandardHypothesesOfScaleHyp

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem ptWide_at_record_gap : ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → Formalism.L2.SG.RowsConc.TFrameAt D → VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 C := by
  intro Cg cb Cu cT CT C0
  have hDB : GlobalTheory.GapIn.Hyp := GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.uniqGap_and_besselOfW.1
  have hBp : BpJoin.ThmBpDS := GlobalTheory.discreteSeriesCoef_pointwiseBound
  obtain ⟨Cgf, hOB⟩ := GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp hDB
  obtain ⟨Cf, hCf, hFrm⟩ := GlobalTheory.FrameTurn.frameChange_of_frames 1 Cgf 2 zero_le_one (by norm_num)
  obtain ⟨Cb, Cg₀, hB⟩ := GlobalTheory.bp_forms_of_gapIn_thmBpDS hDB hBp 1
  obtain ⟨Ca, hCa, hAmp⟩ := GlobalTheory.AmpBesselGap.ampIsBessel hDB Cg cb Cu cT CT C0 1
  refine ⟨max (Ca + max (max 2 Cu) (max CT (1 / 8 + 2 * Cg)) * (Cf + max Cb 0 + Cf * max Cb 0)) (max Cb 0),
    fun Cn => ?_⟩
  obtain ⟨m₀, hm₀⟩ := hAmp Cn
  obtain ⟨Cs₀, hCs₀⟩ := hFrm Cn
  obtain ⟨thr, hthr⟩ := GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses (max m₀ (max (128 * |max Cg₀ Cs₀|) (200 * |Cn|)))
  refine ⟨thr, fun D large₂ C' Cl hC' hCl hTies hTF => ?_⟩
  intro hH
  obtain ⟨h1000, -, hM, -, hrd, -⟩ := hthr D large₂ C' Cl Cg cb Cu cT CT hC' hCl hH.1
  have hβ2 : (2 : ℝ) ≤ max (max 2 Cu) (max CT (1 / 8 + 2 * Cg)) := le_trans (le_max_left _ _) (le_max_left _ _)
  have hStd : Bridge.StdOfHyp D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cg₀ Cs₀) (200 * |Cn|)
      (max (max 2 Cu) (max CT (1 / 8 + 2 * Cg))) :=
    stdOfHyp_rec D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cg₀ Cs₀) (200 * |Cn|) _ (by linarith) zero_le_one hβ2
      (le_trans (le_max_right _ _) (le_max_left _ _))
      (by rw [mul_one]; exact le_trans (le_max_left _ _) (le_max_right _ _))
      (by rw [mul_one]; exact le_trans (le_max_right _ _) (le_max_right _ _))
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM)
      (by
        rw [abs_of_nonneg (by positivity)]
        exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM)
  have h47 : OnePlaceEstimates.UniformityTheoremBPrime D 1 Cn (max Cg₀ Cs₀) (200 * |Cn|) (max Cb 0) :=
    OnePlaceEstimates.upper_bound_mono_constant D zero_lt_one (le_max_left _ _)
      ((hB (max Cg₀ Cs₀) (le_max_left _ _)).2.2 D Cn (200 * |Cn|)
        (mul_le_mul_of_nonneg_left (le_abs_self Cn) (by norm_num)))
  have hFr : Bridge.FrameChange D 1 (max Cg₀ Cs₀) Cn Cf :=
    hCs₀ (max Cg₀ Cs₀) (le_max_right _ _) D (Formalism.MainNotions.OnePlaceExpansion.frame_bound_of_bessel_torus D Cgf 2 le_rfl (hOB D))
  exact AuxiliaryNormPrimes.plancherelBoundOneParameter_of_uniformity D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 Ca 1 Cf (max Cg₀ Cs₀) (200 * |Cn|) _ (max Cb 0) _
    (hm₀ D large₂ C' Cl h1000 hrd (le_trans (le_max_left _ _) hM) hTies.cdScale_tie) hFr hStd (fun _ => hTF) h47
    (by linarith) (le_max_right _ _) hCa hCf (le_max_left _ _) (le_max_right _ _) hH

end GlobalTheory.Core.Deg

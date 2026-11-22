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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeEqHarishChandraOfGapStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBLGapPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Formalism.LocalToGlobal.Columns.ReferenceActionRationalLevels
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFD

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg.CritVand

theorem thrE_add_one_lt (R : Formalism.BasicNotions.Ranks) (h : 1801 ≤ R.r) :
    Formalism.MainNotions.GapDS.thrE (epsSH R) + 1 < 16 * (R.r : ℝ) ^ 19 := by
  have hd : ((2 * R.rS + R.k + 1 : ℕ) : ℝ) = R.r := by exact_mod_cast dimS_eq R
  have hx : (1801 : ℝ) ≤ R.r := by exact_mod_cast h
  have h1 := Formalism.MainNotions.GapDS.thrE_le (epsSH R) (by rw [hd]; linarith)
  rw [hd] at h1
  have h3 : (1 : ℝ) ≤ (R.r : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have h16 : (R.r : ℝ) ^ 3 ≤ (R.r : ℝ) ^ 19 := pow_le_pow_right₀ (by linarith) (by norm_num)
  linarith

theorem vv_eq_vand_of_sizes : ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ), thr ≤ C' → thr ≤ Cl →
    Ties D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → DataNW D → ∀ τ, VV D τ = vand (lamSH D.R (D.hc τ)) := by
  refine ⟨29, fun D large₂ C' Cl Cg cb Cu cT CT hC' hCl hT hH _ τ => ?_⟩
  have hG := Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hH (by linarith) hC'
  have hgap := Formalism.L2.SG.Pf.WuBL.gapAtLeast_of D.R (D.hc τ) (hG.2 τ)
  have hds := GlobalTheory.T.formalDegree_eq_harishChandra_of_gap D hT τ _ (Formalism.L2.Col.lamSH_isHCParam (D.hc τ)) hgap (thrE_add_one_lt D.R hG.1)
  have hanti := Formalism.MainNotions.BridgeLemma.szh_anti hH τ
  have hSF : (0 : ℝ) < ∏ i ∈ Finset.range (2 * D.R.rS + D.R.k + 1), (i.factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  unfold VV
  rw [hds, Formalism.MainNotions.BridgeLemma.szh_fdegHC _ hanti, ← dimS_eq D.R]
  exact div_mul_cancel₀ _ hSF.ne'

end GlobalTheory.Core.Deg.CritVand

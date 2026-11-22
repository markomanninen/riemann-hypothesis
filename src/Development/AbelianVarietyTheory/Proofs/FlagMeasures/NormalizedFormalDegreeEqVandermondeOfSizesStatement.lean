module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFormalDegreeEqVandermondeOfSizes
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

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedFormalDegree_eq_vandermonde_of_sizes : ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → DataNW D → ∀ τ, VV D τ = vand (lamSH D.R (D.hc τ)) := by
  first | exact @GlobalTheory.Core.Deg.CritVand.vv_eq_vand_of_sizes | exact GlobalTheory.Core.Deg.CritVand.vv_eq_vand_of_sizes | (intros; apply GlobalTheory.Core.Deg.CritVand.vv_eq_vand_of_sizes <;> assumption)

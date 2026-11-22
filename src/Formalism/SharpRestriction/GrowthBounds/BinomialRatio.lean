module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FamilyFourthBound
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentStatementHolds
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeAlternative
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KapCore
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TopDegreeLeTwoB
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ExtendedStatementOfParts
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TotalDegreeEplus
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FirstCoefficientFacts
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.LeAndHalfLeProdOneSubExpNegOfBounds
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FinrankTensor
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegLow
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.RankOnDigitsCast
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CardEqChainSum
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.StWeyl
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FactorsOfPerturb
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ChainDim
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.UpperCountOfTopRows
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountLow
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.BlockInj
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.AiAddMulLeA0
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.BlockFG
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ThresholdStandardLarge
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeRatioConsecutive
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairLift
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairCount
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.NotKept
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.WtBound
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KeptBlocksOfSLine
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bracket
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KeptBlocksHolds
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreesLargeOfStd
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseThresholdRatioConsecutive
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SymInt
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.WittPNe
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FinalTheorems
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideEdge
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.DualLat
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSidePos
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SettingCharZeroAt
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SettingCZ

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem closed_extendedAllConclusions {D : Formalism.BasicNotions.D7} (h3 : adm3 D) (hU : RestUp) (hL : RestLow) (hL1 : PartnersToFactors)
    (hLift : RestLift) : Closed (ExtendedAllConclusions D) :=
  have hA2 : RemainderSegmentBoundSecond D := restAlt2_of (restSegLow_of hL) (dimHH_of h3) charZeroAt
  closed_of_rests (fun _ _ _ => segment_statement_holds D _ _ _) (restFree D) (remainderSegmentBoundFirst D) (rest2 D) (restAlt3 D)
    (one_segment_of_upper_lower hU hL) hA2 (restExt_of restRk hL1 hLift hA2)

theorem dimYAt_of_adm {D : Formalism.BasicNotions.D7} (hA : admitted D) : DimYAt :=
  dimY_of (D := D) hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.1 (stWeylAt D)

def Open : Prop := RestPairLift

theorem stmtEExt_of {D : Formalism.BasicNotions.D7} (h : admitted D → Open) : ExtendedClosedForm D := fun hA =>
  have hPL := h hA
  have hY := dimYAt_of_adm hA
  have hCD : ChainDimAt := chainDim_of hY
  have hNB : NumBranchAt := numBranch_of hA.2.1 hA.2.2.1
  have hT : RestTail := restTail_of hCD hNB restPairCount (restNotKeptWt_of (wtBound_of hCD) (restBracket_of (restPairFacts_of restNUp) coarse_degrees_large_holds))
  have hK2 : LeadingRowsBeyondThreshold := top_rows_bound_holds
  have hB : BlockRankAt := blockRankAt
  have hK4 : KeptBlocksBeyondThreshold := kept_blocks_holds
  have hL1 : PartnersToFactors := partners_to_factors_holds
  have hCU : RestCountUp := upper_count_of_top_rows hCD hNB hK2
  have hMU : RestMatchUp := restMatchUp_of (restFirstRows_of (restSTopRows_of hK2))
  have hCL : RestCountLow := restCountLow_of'' hCD hT hMU hK4
  closed_extendedAllConclusions hA.2.2.1 (restUp_of hB hY charZeroAt hCU) (restLow_of hB hY charZeroAt hCL) hL1 (restLift_of (restLiftVec_of hPL))

end Formalism.MainNotions.ColumnSystems.Pf

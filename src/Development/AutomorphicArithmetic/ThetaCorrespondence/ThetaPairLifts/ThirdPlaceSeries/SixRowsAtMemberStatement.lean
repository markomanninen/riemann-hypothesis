module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTwistCoresOverTrueColumnsStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimeColumnValuationsBundlePointsOverColumnStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ReferencePeriodIntegralBundlePointsOfOverColumnsStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedPeriodsIntegralAtBundlePointsStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ReferenceChainEvaluationBundlePointsOverColumnsAStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedChainEvaluationRationalIntegralBundlePoinStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealSideColumnsCompatibleBundlePointsOverColumnsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SixRowsAtMember

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_entries_tie_and_level_valuations_at_built : ∀ (𝒮 : Slots) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.ReferenceChainEvaluationAtBundlePoints S Lk) ∧ (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.TwistedPointAtBundlePoints S Lk) ∧ (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.PeriodAtZeroAtBundlePoints S Lk) ∧ (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.TwistedPeriodAtBundlePoints S Lk) ∧ (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => PeriodEntriesOverColumns.Row_tie S Lk) ∧ (Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => AllBundlePointProperties.LevelPrimeColumnValuationsAtBundlePoints S Lk) := by
  first | exact @_root_.GlobalTheory.Fc.six_rows_at_member_alt | exact _root_.GlobalTheory.Fc.six_rows_at_member_alt | (intros; apply _root_.GlobalTheory.Fc.six_rows_at_member_alt <;> assumption)
end

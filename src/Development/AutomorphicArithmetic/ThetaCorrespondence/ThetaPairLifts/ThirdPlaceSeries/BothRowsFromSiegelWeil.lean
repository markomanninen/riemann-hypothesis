module

public import Mathlib
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Formalism.LocalToGlobal.ThresholdSelection
public import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
public import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
public import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHyperplaneVolumeRatioSiegelWeilStatement
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassNumberAll
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstTypePrimeLargeOfRecord
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExactRanksOfRecord
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimesOverOfNorm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeEqMassOfReal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankConditionOfColumnsEqualSymmetricLevelStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TFrameOfRanksRowThree
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RanksAndFrameOfTiedClassStatement

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions
namespace GlobalTheory
theorem bothRowsFromSiegelWeil_alt :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (𝒞 : FamClass), _root_.Formalism.L2.TwistSelection 𝒞 →
      (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) ∧
        Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 :=
  fun hSW => _root_.GlobalTheory.T.ranksF_tFrame_closed_of_mass_ratio (GlobalTheory.T.unitary_hyperplane_volumeRatio_siegelWeil hSW)
end GlobalTheory
end

module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
public import Development.AutomorphicArithmetic.CharacterBoxes.ExS
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealTiedSetDiv
public import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
public import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfGappedMultiplicity
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkMin
public import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalLinkOfBranchIdentitiesAndMultiplicity
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermRepUnram
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowHTuCTmin

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hTu_cTmin_of_genusMass : (∀ D, MassRatioUnderVolume D) → (∀ D, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.GenusMassAt D 2) → ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), Row Q Lk fun 𝒜 _ => R1.H_hTu (fun _ y => Formalism.MainNotions.StandardLattice.HarishChandraReduction.cTmin y) 𝒜 := by
  first | exact @_root_.GlobalTheory.Fc.row_hTu_cTmin_alt | exact _root_.GlobalTheory.Fc.row_hTu_cTmin_alt | (intros; apply _root_.GlobalTheory.Fc.row_hTu_cTmin_alt <;> assumption)
end

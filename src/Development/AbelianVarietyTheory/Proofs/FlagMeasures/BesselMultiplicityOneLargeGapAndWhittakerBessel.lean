module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.MultiplicityOneUnitaryBranchingOfGapHyp
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.DoubleCosetBesselBoundOfGapConstantLe

@[expose] public section

namespace GlobalTheory

theorem uniqGap_and_besselOfW : GlobalTheory.GapIn.UniqGap ∧ Formalism.L2.SG.LocWSOf.BesselOfW :=
  ⟨CompanionTheory.Lime.BM.uniqGap_holds, Formalism.MainNotions.BridgeCS3dBOW.besselOfW_holds⟩

end GlobalTheory

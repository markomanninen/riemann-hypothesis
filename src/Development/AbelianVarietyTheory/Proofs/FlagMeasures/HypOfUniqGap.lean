module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import CompanionTheory.AutomorphicTheory.PieriRules.InfinitesimalCharacterDiscreteSeries
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanGapSmall
public import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsFD

@[expose] public section

namespace GlobalTheory.GapIn

theorem hyp_of_uniqGap : GlobalTheory.GapIn.UniqGap → GlobalTheory.GapIn.Hyp :=
  fun h => ⟨CompanionTheory.PieriExpansion.hypsG_of_zuck CompanionTheory.Zuck.zuckerman_gap, h, Formalism.L2.SG.OwnFacts.factMultOne.out,
    Formalism.L2.SG.OwnFacts.FD.factDsigHC.out⟩

end GlobalTheory.GapIn

module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SettingExistsMeasured
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.SatakeDualWeyl.StatementC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace Formalism.L2.SG.Pf.Set3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Witt

variable {D : D7}

end Witt

end Formalism.L2.SG.Pf.Set3

namespace Formalism.L2.SG.Pf.Set3

variable (D : D7)

def WBlkExists : Prop :=
  Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (P : AdditiveCharacterData A) (Rf : ReferenceFrame A L)
    (Bu : AutomorphicBundle A P Rf) (Pi : RepresentationData A L) (Mu : MuBlocks A L), Nonempty (WBlk A L Bu Pi Mu)

end Formalism.L2.SG.Pf.Set3

namespace Formalism.L2.SG.Pf.Set3

variable {D : D7}

variable (D)

end Formalism.L2.SG.Pf.Set3

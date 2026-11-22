module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PvalFormExistsAlt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpCovOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PairAmpConstOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

theorem AmpCov_holds {D : D7} {X : HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) : AmpCov Y :=
  ampCov_of Formalism.L2.SG.Pf.ratPt_holds Formalism.L2.SG.Closed.ChiTrivialC_holds Y

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X} {hF : FinX Y} (W : WittDat X)
  (hI : SIso D.s (sOf hF))

end Formalism.L2.SG.Pf.KernelOfEmbedding

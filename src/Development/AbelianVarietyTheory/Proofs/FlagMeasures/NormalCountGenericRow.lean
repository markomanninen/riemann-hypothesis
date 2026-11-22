module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqWire
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNml
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNormals
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlLineHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlIntHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlPtDCHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalCount
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordsNonGenericEstimatesChainStatement

@[expose] public section

open Formalism.L2.SG.Pf.MainEqSteps

namespace GlobalTheory

theorem stepNormalsG_holds : StepNormalsG :=
  Formalism.L2.SG.NGCut.NormalInvariants.Gen.stepNormalsG_of
    (Formalism.L2.SG.Pf.nmlInvG_of Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine_holds
      Formalism.L2.SG.NGCut.NormalIntegrality.NmlInt_holds Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep_holds)
    Formalism.L2.SG.NGCut.NormalCount.NormCount_holds
    GlobalTheory.T.equalWords_nonGeneric_estimates_chain.2.2.2.1

end GlobalTheory

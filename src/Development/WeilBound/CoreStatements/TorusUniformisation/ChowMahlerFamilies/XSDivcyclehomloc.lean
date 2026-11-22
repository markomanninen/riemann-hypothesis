module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegreeCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleHomLoc
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingIsLocal
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingNoetherian
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingDimLe
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingLocal

@[expose] public section

namespace PositivityTheory.Xgn.A_s_divcyclehomloc

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem homLocRingLocal : HomLocRingLocal.Statement.{0} :=
  HomLocRingLocal.proof (HomLocRingIsLocal.proof HomLocRingMem.proof)
    (HomLocRingNoetherian.proof HomLocRingMem.proof)
    (HomLocRingDimLe.proof HomLocRingMem.proof (HomLocRingIsLocal.proof HomLocRingMem.proof))

end PositivityTheory.Xgn.A_s_divcyclehomloc

theorem PositivityTheory.Xgn.t_s_divcyclehomloc : GroundTheory.Heights₂.Heights.NumbersDVR.DivCycleHomLoc.Statement.{0} :=
  GroundTheory.Heights₂.Heights.NumbersDVR.DivCycleHomLoc.proof PositivityTheory.Xgn.A_s_divcyclehomloc.homLocRingLocal

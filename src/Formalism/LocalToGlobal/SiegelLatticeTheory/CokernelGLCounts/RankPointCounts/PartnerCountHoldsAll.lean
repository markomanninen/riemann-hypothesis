module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PcBridgeB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IntegralClosureRankAndResidueTrdegLe
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PcIntGen

@[expose] public section

namespace Formalism.L2.SG.Pf.PCount

theorem partnerCount_holds_all {D : Formalism.BasicNotions.D7} (Zd : Formalism.L2.SG.TermLoc.LocDat D) : PartnerIsomorphismCount Zd :=
  partnerCount_of_iso Zd (Formalism.L2.SG.LsDatumA.integralClosureRank_and_residueTrdegLe D) (intGenP_holds Zd) BI.integralIsomorphism_holds

end Formalism.L2.SG.Pf.PCount

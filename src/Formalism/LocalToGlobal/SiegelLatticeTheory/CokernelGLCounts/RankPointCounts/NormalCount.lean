module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CardMulConjEqLeOfFractionalIdeal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalInvariants
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.VanishingOrbitalPoints
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup

@[expose] public section

namespace Formalism.L2.SG.NGCut.NormalCount

theorem NormCountG_holds : Formalism.L2.SG.NGCut.NormalInvariants.NormCountG := by
  intro E _ _ _ J m hJ hm S hS
  exact Formalism.L2.SG.NGCut.TorsionTotientBound.card_mul_conj_eq_le_of_fractionalIdeal E J m hJ hm S hS

theorem NormCount_holds : Formalism.L2.SG.NGCut.NormalInvariants.NormCount :=
  Formalism.L2.SG.NGCut.NormalInvariants.normCount_of NormCountG_holds

end Formalism.L2.SG.NGCut.NormalCount

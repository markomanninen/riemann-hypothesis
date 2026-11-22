module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetMomentsOfUnitPeriod
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqAndAlg
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeFactsAll
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitPeriodTranslatesMomentsFiniteStatement

@[expose] public section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomTop

theorem jetMoments : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments :=
  GlobalTheory.MomT.jetMoments_of_unitPeriod
    (GlobalTheory.T.unitPeriodTranslates_moments_finite GlobalTheory.MomEq.eq_and_alg.1 GlobalTheory.MomEq.eq_and_alg.2)
    GlobalTheory.MomEq.eq_and_alg.1 GlobalTheory.MomLat.latticeFactsAll

end GlobalTheory.MomTop

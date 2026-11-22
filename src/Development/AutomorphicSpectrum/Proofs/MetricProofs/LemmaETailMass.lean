module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailMass
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETailMass
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETrunc
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETruncMass
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETruncTail
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaEScale
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaEEnergy
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaEWeight
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLogNormSecIntegrable

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Giv


open GroundTheory.Heights₂.Heights.AnalyticLimit in
theorem lemmaETailMass : GroundTheory.Heights₂.Heights.AnalyticLimit.LemmaETailMass.Statement :=
  LemmaETailMass.proof LemmaETrunc.proof LemmaETruncMass.proof
    (LemmaETruncTail.proof LemmaEScale.proof LemmaEEnergy.proof LemmaEWeight.proof
      LogNormSecIntegrable.proof)

end GlobalTheory.CompanionTheory.Ar.Giv

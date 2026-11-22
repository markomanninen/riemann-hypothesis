module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemPair
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemPairJ
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflTrace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FinTrace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.RamOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FinAct
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobFacts

@[expose] public section

namespace UpperTheory.Gal.InertialTypesAlt.L

theorem elemPairJ_holds : UpperTheory.Gal.Join.ElemPairJ := elemPairJ elemPair

theorem finTrace_holds (h : GlobalTheory.DZA.InflMatching) (h₁ : G.VarEx) (h₂ : G.VarTrace) (h₃ : G.NormInt) : FinTrace :=
  finTrace resEx finAct inflFacts frobFacts (inflTrace h h₁ h₂ h₃)

end UpperTheory.Gal.InertialTypesAlt.L

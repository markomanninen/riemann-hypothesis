module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ComplexMultiplicationJacquetShalikaStatement

@[expose] public section

namespace GlobalTheory.CompanionTheory.CM

theorem idealInvariantsOneOrbit : GlobalTheory.Published.IdealInvariantsOneOrbitSt :=
  GlobalTheory.Published.ComplexMultiplicationJSt.oneOrbit GlobalTheory.T.complex_multiplication_jacquet_shalika

end GlobalTheory.CompanionTheory.CM

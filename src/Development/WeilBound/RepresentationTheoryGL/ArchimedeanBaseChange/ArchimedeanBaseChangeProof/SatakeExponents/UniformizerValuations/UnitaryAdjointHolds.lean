module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SphericalHeckeUnitary.PuSphHecke
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.QuadraticCharacterNorms.SphStarUPlug
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalAlgebraHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebraStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactUnitHoldsStatement

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.U

theorem unitary_words_holds : UWord :=
  UU.uWordOfU GlobalTheory.T.diagonal_algebra_holds GlobalTheory.T.local_algebra_holds (GlobalTheory.T.spherical_one_of_local_algebra GlobalTheory.T.local_algebra_holds) GlobalTheory.T.compact_unit_holds PositivityTheory.Rg.BcB.F.Fok.sphStarU

theorem unitary_adjoint_holds : UAdj :=
  UU.uAdjOfU GlobalTheory.T.diagonal_algebra_holds GlobalTheory.T.local_algebra_holds (GlobalTheory.T.spherical_one_of_local_algebra GlobalTheory.T.local_algebra_holds) GlobalTheory.T.compact_unit_holds PositivityTheory.Rg.BcB.F.Fok.sphStarU

end PositivityTheory.Rg.BcB.F.U

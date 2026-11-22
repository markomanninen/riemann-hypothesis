module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.EFinalOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.IsometrySymmetry.IsoVSymm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitVectorIdentityStatement

@[expose] public section

namespace PositivityTheory.Rg.BcB.SpectralAccumulation

theorem eisenstein_final_of_separation (hS : Sep4) : EFinal :=
  eFinal_of hS FiniteDiscreteTypes.finDisc (GlobalTheory.T.limit_vector_identity : LimVec)

end PositivityTheory.Rg.BcB.SpectralAccumulation

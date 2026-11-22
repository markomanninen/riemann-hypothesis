module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ComapTwKer
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.DerFin
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.JacquetModuleThetaTwist
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.NontrivialOfIsIrreducible
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.CuspPair
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi

@[expose] public section

namespace PositivityTheory.RgGu.NR

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nuPair : GlobalTheory.BZSeg.NuPair k :=
  nuPair_of k (GlobalTheory.T.derivative_jacquet_holds k GlobalTheory.CompanionTheory.BZCuspPair.irrAdm) (jmTheta k) (derFin_of k (derEquiv k))

theorem cuspPairIrr : GlobalTheory.BZSeg.CuspPairIrr k := cuspPairIrr_of k (nuPair k)

end PositivityTheory.RgGu.NR

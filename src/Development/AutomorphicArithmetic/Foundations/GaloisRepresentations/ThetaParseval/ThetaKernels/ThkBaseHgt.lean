module

public import Development.WeilBound.ThetaLifts.LatticeBasics.HgtInt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseStmt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseHgtInt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Stab2CptK

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
namespace GlobalTheory.ThK.Dbl
theorem hgtEx_k : _root_.GlobalTheory.ThK.Dbl.HgtEx_k := _root_.GlobalTheory.ThK.Dbl.hgtEx_of_k _root_.GlobalTheory.ThK.Dbl.stab2Cpt_k
end GlobalTheory.ThK.Dbl
end

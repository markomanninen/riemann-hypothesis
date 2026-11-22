module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CentralPositiveSemidefinite.ContinuousOnPullbackCentralScalingSimplexParam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CentralPositiveSemidefinite.LamSApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CentralPositiveSemidefinite.ActLEqOfScalar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CentralPositiveSemidefinite.RealSmulPosSemidef

@[expose] public section

namespace PositivityTheory.KB

theorem sCen_of (hEv : SEv) : SCen :=
  CentralizerFixed.join (fun L _ _ => CentralizerFixed.span_units (L := L)) CentralizerFixed.tScal CentralizerFixed.tSimp
    (CentralizerFixed.tAv_of CentralizerFixed.tScal CentralizerFixed.tSimp) hEv

end PositivityTheory.KB

module

public import Development.AutomorphicArithmetic.ShortNorms.SmallOneOf
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesImagQuadShortIntervalLowerBoundStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimesInProgressionsRelativeErrorStatement

@[expose] public section

theorem UpperTheory.T3.shortNorm : UpperTheory.T3.ShortNorm := GlobalTheory.T.normPrimesImagQuad_short_interval_lower_bound

theorem UpperTheory.T3.smallOne : UpperTheory.T3.SmallOne := UpperTheory.T3.smallOne_of GlobalTheory.T.primesInProgressions_relativeError

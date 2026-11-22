module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTraceSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoeffShapeSmoothCompactSupport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffPolynomialConjugationDerivMemShapeSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyCoeffVectorsLieInFiniteDimensionalSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShapeIntegratedOperatorRangesPolynomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTraceSumInnerOfRangeLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumInnerMulInnerProj

@[expose] public section

namespace GlobalTheory.PsCo.Pc3

theorem stTrAd : GlobalTheory.PsCo.Pc1.StTrAd :=
  stTrAd_of
    GlobalTheory.ShapeSmoothFinite.stShape
    GlobalTheory.PsCo.Pc1.B.cutoffPolynomial_conjugation_deriv_mem_shapeSpan
    uFin rangeShape
    GlobalTheory.OpTrace.hasTrace_sum_inner_of_range_le
    GlobalTheory.Pc3.conjDeriv

end GlobalTheory.PsCo.Pc3

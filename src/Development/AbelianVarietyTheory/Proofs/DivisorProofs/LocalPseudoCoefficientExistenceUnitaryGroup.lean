module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfConstOfTendsto
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuPowLambdaProductCoeffMuVariablePencilEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StProfileHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCutFnIteratedDerivScale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffIter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFamF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoeffShapeSmoothCompactSupport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbIntAdSpanEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StOrbCpt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactCentOfConj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumInnerIntegralEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StTrAd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactPseudoCoefficientDataStatement

@[expose] public section

open GlobalTheory.PsCo.Pc1

namespace GlobalTheory.PsCo.Pc

theorem localPC_holds : LocalPC :=
  GlobalTheory.PsCo.Pc1.localPC_of_steps GlobalTheory.PsCo.Pc1.A.stAlg GlobalTheory.PsCo.Pc1.stProfile_holds
    GlobalTheory.PsCo.Pc1.stFam GlobalTheory.PsCo.Pc1.Homot.stHomot GlobalTheory.PsCo.Pcd.stLim
    GlobalTheory.ShapeSmoothFinite.stShape GlobalTheory.PsCo.Pc1.orbInt_adSpan_eq_zero GlobalTheory.PsCo.Pc1.stOrbCpt
    GlobalTheory.PsCo.NonEll.stNonEll GlobalTheory.PsCo.Pc3.stTr GlobalTheory.PsCo.Pc3.stTrAd GlobalTheory.T.maximalCompact_pseudoCoefficientData

end GlobalTheory.PsCo.Pc

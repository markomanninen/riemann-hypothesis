module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOfCompact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerLinOfKerBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CntBasicOfKerBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowIntOfKerBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColSqOfKerBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowsColumnsSquareIntegrable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralWeightedSqLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralEnormRpowTwoNeTop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchurOpOfSchurL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableReflect
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerMulOfKerBasicOfCvTest
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoeFnSumAe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerEqIntegralConjMul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompKey
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColOp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellSumOfCntBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoUnif
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpEx
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CvAdjEqAvg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerClose
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecCloseOfKerBasicColSq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecNormOfVecClose
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAtOfSqBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecInnerOfKerBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecLimOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfLeSmall

@[expose] public section

namespace PositivityTheory.Rg.BcB.E1

theorem kerBasic : KerBasic := GlobalTheory.CompanionTheory.KernelBasic.kerBasic
theorem kerLin : KerLin := GlobalTheory.CompanionTheory.KerLinear.kerLin_of_kerBasic kerBasic
theorem cntBasic : CntBasic := GlobalTheory.CompanionTheory.KernelCount.cntBasic_of_kerBasic kerBasic
theorem rowInt : RowInt := GlobalTheory.CompanionTheory.KernelRows.rowInt_of_kerBasic kerBasic
theorem colSq : ColSq := GlobalTheory.CompanionTheory.KernelColumn.colSq_of_kerBasic kerBasic
theorem kernel_rows_columns_square_integrable : KernelL2RowsColumns := GlobalTheory.CompanionTheory.KerSquare.kernel_rows_columns_square_integrable kerBasic cntBasic colSq
theorem schurL : SchurL := GlobalTheory.CompanionTheory.Schur.schurL
theorem schurInt : SchurInt := GlobalTheory.CompanionTheory.SchurKernel.schurInt_of_schurL schurL
theorem schurOp : SchurOp := GlobalTheory.CompanionTheory.Schur.schurOp_of_schurL schurL
theorem cvTest : CvTest := GlobalTheory.CompanionTheory.ConvTest.cvTest
theorem kerMul : KerMul := GlobalTheory.CompanionTheory.KernelComposition.kerMul_of_kerBasic_of_cvTest kerBasic cvTest
theorem opExA : OpExA := GlobalTheory.CompanionTheory.OpEx.opExA kerBasic rowInt schurOp
theorem opAdj : OpAdj := GlobalTheory.CompanionTheory.KerAdj.opAdj_of kerBasic rowInt schurInt opExA
theorem opMul : OpMul := GlobalTheory.CompanionTheory.KernelOperators.opMul kerBasic kerLin rowInt kernel_rows_columns_square_integrable schurInt cvTest kerMul
theorem colOp : ColOp := GlobalTheory.CompanionTheory.KernelColumns.colOp kerBasic cvTest kernel_rows_columns_square_integrable kerMul
theorem cellSum : CellSum := GlobalTheory.CompanionTheory.CellSumProof.cellSum_of_cntBasic cntBasic
theorem twoUnif : TwoUnif := GlobalTheory.CompanionTheory.TwoSidedUnif.twoUnif
theorem bumpEx : BumpEx := GlobalTheory.CompanionTheory.Bump.bumpEx
theorem approxU : ApproxU := GlobalTheory.CompanionTheory.ApproxUnit.approxU cvTest twoUnif
theorem kerClose : KerClose := GlobalTheory.CompanionTheory.KernelClose.kerClose
theorem vecClose : VecClose := GlobalTheory.CompanionTheory.KernelColumns.vecClose_of_kerBasic_colSq kerBasic colSq
theorem vecNorm : VecNorm := GlobalTheory.CompanionTheory.KernelColumns.vecNorm_of_vecClose vecClose
theorem vecEx : VecEx := GlobalTheory.CompanionTheory.KerVec.vecEx cntBasic kernel_rows_columns_square_integrable twoUnif vecClose
theorem vecInner : VecInner := GlobalTheory.CompanionTheory.E1.vecInner_of_kerBasic kerBasic
theorem vecLim : VecLim := GlobalTheory.CompanionTheory.KernelColumns.vecLim_of cntBasic cvTest colOp approxU vecClose
theorem ptEq : PtEq := GlobalTheory.CompanionTheory.KerPoint.ptEq_of kerBasic cvTest opAdj colOp bumpEx approxU kerClose vecLim

end PositivityTheory.Rg.BcB.E1

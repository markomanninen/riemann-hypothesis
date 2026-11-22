module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.LatSum
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UnitsCpt
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.WtNonneg
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThCont
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MeanZero
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.HermitianMatrixBasisOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.HermitianStandardVector
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.RatGl
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPartAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharInt
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftIsBoundedCuspidal
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Dens
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.DMOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MomKill
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbFn
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CoefPer
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Rev

@[expose] public section

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

theorem maj_holds : Maj := maj latSum decE

theorem meanZero_holds : MeanZero := meanZero decE

theorem thetaConstantTerm_eq : ThetaLiftEqAnisotropicPart := f0Eq maj_holds thCont meanZero_holds (rank1 decE maj_holds orb1)

theorem rev_holds : Rev :=
  rev thetaConstantTerm_eq (coef maj_holds thCont) (thetaPairing_constantTerm_cuspidal maj_holds thCont thetaConstantTerm_eq (coef maj_holds thCont)) dens (fub maj_holds thCont)
    (coefPer decE maj_holds orbS momKill (orbFn orbS))

end UpperTheory.ConvolutionTheory.RankTwoDescent

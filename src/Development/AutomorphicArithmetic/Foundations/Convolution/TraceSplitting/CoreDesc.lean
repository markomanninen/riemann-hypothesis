module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreDescOf
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.AbsLast
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PullBack
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.UnitTrace
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.OneTerm
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SideSum
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PickS
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PickInf
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.TyEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.FdFixed
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.GoodEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursBasics
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic

@[expose] public section

open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T in
theorem UpperTheory.ConvolutionTheory.T.coreDesc :
    UpperTheory.ConvolutionTheory.CI → UpperTheory.ConvolutionTheory.GM.GM → UpperTheory.ConvolutionTheory.T.CoreDesc :=
  coreDesc_of absLast pullBack unitTrace oneTerm sideSum pickS pickInf tyEx termE goodEx places C.occursBasics L1.eigBasic

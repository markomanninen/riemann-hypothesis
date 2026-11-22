module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.TyExOf
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitLev
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStableAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitMatch
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.InertData
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.OffStable
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TypedEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic

@[expose] public section

open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T in
theorem UpperTheory.ConvolutionTheory.T.tyEx :
    UpperTheory.ConvolutionTheory.T.TyEx :=
  tyEx_of splitLev splitStable splitMatch inertData offStable L1.typedEx L1.eigBasic

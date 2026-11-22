module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
public import Development.WeilBound.NonsplitUniqueness.Places

@[expose] public section

theorem UpperTheory.ConvolutionTheory.T.places :
    UpperTheory.ConvolutionTheory.T.Places := PositivityTheory.tft.places_holds

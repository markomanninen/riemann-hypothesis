module

public import Formalism.PolynomialDimension.MultinomialDepth.SecondParameterSizeBoundsHolds
public import Formalism.PolynomialDimension.MultinomialDepth.SecondParameterSlackBoundsHolds
public import Formalism.PolynomialDimension.MultinomialDepth.FrameMultinomialBoundHolds
public import Mathlib
public import Formalism.PolynomialDimension.StatementNum
public import Formalism.PolynomialDimension.WeylDim

@[expose] public section

namespace Formalism.CountingSumsFrames.Top

theorem paramsII0 : Formalism.CountingSumsFrames.ParamsII0 := Formalism.CountingSumsFrames.secondParameterSizeBounds_holds
theorem paramsII5 : Formalism.CountingSumsFrames.ParamsII5 := Formalism.CountingSumsFrames.secondParameterSlackBounds_holds

end Formalism.CountingSumsFrames.Top

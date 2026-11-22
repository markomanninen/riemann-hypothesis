module

public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.MinkCore
public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.GjLevel
public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.GjScale
public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.SuccMin
public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.AdaptedBasis
public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.MeasureEqCovolumeMulVolumeImage
public import Mathlib
public import Formalism.SuccessiveMinima.DefsMink

@[expose] public section

namespace Formalism.FN

theorem minkowskiIIUpper : MinkowskiIIUpper :=
  minkowskiIIUpper_of (minkCore_of partialBoxVolumeMonotoneStep partialBoxVolumeScaling) existsSuccessiveMinimaVectors
    existsAdaptedBasis

end Formalism.FN

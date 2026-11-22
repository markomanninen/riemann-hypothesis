module

public import Formalism.ZeroFreeRegion.FinalZFR
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.SmallHeightLogDeriv
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivRegionOf
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Perron
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.RectDoublePole
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LaurentAtOne
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.RectShiftOf
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.GzPNTOf

@[expose] public section

noncomputable section

namespace Formalism.ZF

theorem logDerivRegion : LogDerivRegion :=
  logDerivBoundInRegionOfBounds zeroFreeRegion logDerivBoundRightHalfPlane growthBound zetaInvBound_statement
    logDerivBoundedHeight landauLocal

theorem rectShift : RectShift := rectangleShiftOfResidue rectangle_double_pole laurentExpansionAtOne

theorem gzPNT : GzPNT :=
  zetaPrimeSumErrorBoundOfBounds zeroFreeRegion logDerivRegion logDerivBoundRightHalfPlane perron_formula rectShift

end Formalism.ZF

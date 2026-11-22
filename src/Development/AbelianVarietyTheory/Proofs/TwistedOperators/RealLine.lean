module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestRealPlacesDefinitePeriodsOnOneLineStatement

@[expose] public section

namespace GlobalTheory.RowReal

open GlobalTheory.RowClaim

theorem realLine : Big fun ch => RealLine ch :=
  big_mono (fun ch h => realLine_of_periodsOnLine ch h) GlobalTheory.T.rowTest_realPlaces_definitePeriods_onOneLine

end GlobalTheory.RowReal

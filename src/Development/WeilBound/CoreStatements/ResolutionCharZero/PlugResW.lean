module

public import Mathlib
public import Development.ResolutionOfSingularities.HasSimpleNormalCrossingsOfInStrictNormalCrossing
public import Development.WeilBound.CoreStatements.ResolutionCharZero.FromRes

@[expose] public section

namespace PositivityTheory.ResPlug.FromRes

theorem resW : PositivityTheory.ResPlug.ResW :=
  resW_of_functorialResolution FunctorialResolution.functorialResolutionCharZero.{0}

end PositivityTheory.ResPlug.FromRes

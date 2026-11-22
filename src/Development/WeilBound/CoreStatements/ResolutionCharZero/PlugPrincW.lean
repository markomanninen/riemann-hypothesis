module

public import Mathlib
public import Development.ResolutionOfSingularities.HasSimpleNormalCrossingsOfInStrictNormalCrossing
public import Development.WeilBound.CoreStatements.ResolutionCharZero.FromRes

@[expose] public section

namespace PositivityTheory.ResPlug.FromRes

theorem princW : PositivityTheory.ResPlug.PrincW :=
  princW_of_functorialPrincipalization FunctorialResolution.functorialPrincipalizationCharZero.{0}

end PositivityTheory.ResPlug.FromRes

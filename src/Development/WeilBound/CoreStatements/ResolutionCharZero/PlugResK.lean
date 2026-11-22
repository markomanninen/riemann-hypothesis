module

public import Mathlib
public import Development.WeilBound.CoreStatements.ResolutionCharZero.PlugResW
public import Development.WeilBound.CoreStatements.ResolutionCharZero.PlugPrincW

@[expose] public section

namespace PositivityTheory.ResPlug.FromRes

theorem resK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement :=
  PositivityTheory.ResPlug.resK_of_weak resW princW

end PositivityTheory.ResPlug.FromRes

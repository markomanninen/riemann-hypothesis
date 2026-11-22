module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.CharMain

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

theorem char (hx : Ext.All) : CharStatement :=
  ChA.char_main hx

end ReciprocityTheory.ChartRestriction.G.I2

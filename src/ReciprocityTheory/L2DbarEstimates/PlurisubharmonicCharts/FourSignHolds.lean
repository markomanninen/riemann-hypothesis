module

public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.HyPhi
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxL
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeLoc
public import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.DifferentiableAtChart
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeI
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ImportsAlt
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ZeroDimA
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourIndep
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourBasic

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Y

section
variable (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La]

end

theorem four_sign_holds (f : ℕ) : FOURSignStatement f :=
  four_sign f (four_indep f) (four_bound f)

end ReciprocityTheory.L2DbarEstimates.Y

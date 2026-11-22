module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsBergDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AParamStA
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.ExistsAnalyticGraphChartMvPolynomial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology

variable {J : Type} [Fintype J] {D : ℕ}

theorem adens_maDensity_eq_maDens (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    maDensity φ z = ReciprocityTheory.AnForm.maDens φ z := rfl

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

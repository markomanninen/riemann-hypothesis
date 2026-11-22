module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XFibStereo

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.sphere_measure_stereographic_integral :
    let n : ℂ → Fin 3 → ℝ := fun a i =>
      (![2 * a.re, 2 * a.im, 1 - ‖a‖ ^ 2] : Fin 3 → ℝ) i / (1 + ‖a‖ ^ 2)
    (∀ f : (Fin 3 → ℝ) → ℝ, Measurable f →
      (Integrable (fun a : ℂ => f (n a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) ↔
        Integrable (fun m : ReciprocityTheory.ChartRestriction.G.AI.S2 =>
          f (fun i => (m : ReciprocityTheory.ChartRestriction.G.AI.E3) i))
          ReciprocityTheory.ChartRestriction.G.AI.sphereMeasure) ∧
      (∫ a : ℂ, f (n a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) =
        (∫ m : ReciprocityTheory.ChartRestriction.G.AI.S2,
          f (fun i => (m : ReciprocityTheory.ChartRestriction.G.AI.E3) i)
          ∂ ReciprocityTheory.ChartRestriction.G.AI.sphereMeasure)) ∧
    (∀ a₀ a₁ : ℂ, logSin 1 a₀ a₁ = (1 / 2) * Real.log ((1 - (∑ i, n a₀ i * n a₁ i)) / 2)) := by
  intro n
  exact ⟨PositivityTheory.Xgp.fib_stereo.measure_part, PositivityTheory.Xgp.fib_stereo.logSin_part⟩

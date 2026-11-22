module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientIntegralBound.QuotientLIntegralLeMultiplicityLIntegral

@[expose] public section

theorem poincareSeries_finite (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesFinite G μ :=
  PI.PoincareSeriesFinite.UnitaryGroupMassFormula.poincareSeriesFinite G μ

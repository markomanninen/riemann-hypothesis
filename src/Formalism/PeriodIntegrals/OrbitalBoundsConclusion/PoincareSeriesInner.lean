module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ComplexDoubleCosets.FoldL2ComplexOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ComplexDoubleCosets.ComplexDoubleCoset

@[expose] public section

theorem fold_l2_bound_c (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesInner G μ :=
  PI.PoincareSeriesInner.W.fold_L2_complex_of PI.PoincareSeriesInner.W.complex_double_coset G μ

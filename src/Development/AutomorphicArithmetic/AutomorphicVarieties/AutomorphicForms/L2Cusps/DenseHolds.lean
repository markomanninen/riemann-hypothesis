module

public import GroundTheory.AutomorphicForms.L2LocalComponents

@[expose] public section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum

theorem UpperTheory.V.KernelIndexFullLattice.dense_holds (K : Type) [Field K] [NumberField K]
    (n : ℕ) (μ₁ : Measure (Reduction.normOneGL (K := K) (n := n))) [μ₁.IsHaarMeasure] :
    ((centralCuspForms K n).map (cuspVecL μ₁)).topologicalClosure = ⊤ :=
  topologicalClosure_map_centralCuspForms μ₁

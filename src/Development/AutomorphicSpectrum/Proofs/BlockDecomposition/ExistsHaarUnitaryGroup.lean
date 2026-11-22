module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv

@[expose] public section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.ModelS

theorem exists_rightInvariant_measure_unitaryGroup
    (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]
    [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] :
    ∃ κ : Measure (Matrix.unitaryGroup (Fin n) ℂ),
      IsFiniteMeasure κ ∧ κ.IsMulRightInvariant ∧ κ.IsOpenPosMeasure := by
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) :=
    GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  let μ : Measure (Matrix.unitaryGroup (Fin n) ℂ) := Measure.haarMeasure ⊤
  refine ⟨μ.inv, inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.CompanionTheory.ModelS

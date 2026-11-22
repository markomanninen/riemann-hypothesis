module

public import Mathlib
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant

@[expose] public section

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.UpqHaarRight

theorem isMulRightInvariant :
    ∀ (P Q : ℕ) (μ : Measure (UpqT P Q)), μ.IsHaarMeasure → μ.IsMulRightInvariant :=
  fun P Q μ hμ => GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure P Q μ hμ

end GlobalTheory.UpqHaarRight

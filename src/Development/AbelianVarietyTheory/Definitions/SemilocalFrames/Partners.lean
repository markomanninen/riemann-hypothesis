module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq

@[expose] public section

noncomputable section

open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc Matrix

namespace GlobalTheory.SgDen

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]


def densF (q : ℕ) (η : ℝ) (n a c : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc (n + 1 - a - c) n, (1 - (η * (q : ℝ)⁻¹) ^ i)

variable [MeasurableSpace E]


end GlobalTheory.SgDen

module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
public import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl

@[expose] public section

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Filter Topology

noncomputable section

namespace GlobalTheory.FlagAr

open GlobalTheory.FlagPoly

variable {D : D7} (Y : ShimX D.what₂.Tau)

def setB (B : ℝ) : Finset ℕ :=
  ((Finset.range (⌊B⌋₊ + 1)).filter Nat.Prime) ∪
    (Nat.primeFactors (2 * (NumberField.discr D.host.E).natAbs) ∪ Y.lev)

end GlobalTheory.FlagAr

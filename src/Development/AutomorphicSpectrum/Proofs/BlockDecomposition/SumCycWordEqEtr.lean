module

public import Mathlib
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
public import Formalism.PeriodIntegrals.DSInfCharCap
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ElementaryTracePowerCyclicWords

@[expose] public section

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CycWordTrace

theorem sum_cycWord_eq_etr : ∀ (B : Type) [Ring B] (n m : ℕ) (X : Fin n → Fin n → B),
    ∑ a : Fin (m + 1) → Fin n, ((GlobalTheory.Dec.cycWord a).map fun p => X p.1 p.2).prod
      = Formalism.REAL.etr X (m + 1) := by
  intro B _ n m X
  exact (GlobalTheory.TraceCycWord.etr_succ_eq_sum_cycWord X m).symm

end GlobalTheory.CompanionTheory.CycWordTrace

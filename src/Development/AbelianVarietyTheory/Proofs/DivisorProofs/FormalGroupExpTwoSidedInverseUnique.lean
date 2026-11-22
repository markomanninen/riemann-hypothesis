module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.RootStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.FactorialWeightedSumBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.OmBStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsExpEqOfSubstLg

@[expose] public section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem expOf_twoSided_unique : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (d : ℕ) (G : LogFGL v d), IsExp G (expOf G) ∧ (∀ a, subst G.lg (expOf G a) = X a) ∧
      ∀ ex, IsExp G ex → ex = expOf G := by
  intro C _ _ v d G
  obtain ⟨h1, h2, h3⟩ := expOf_spec G
  exact ⟨h1, h3, h2⟩

end GlobalTheory.FGDepth

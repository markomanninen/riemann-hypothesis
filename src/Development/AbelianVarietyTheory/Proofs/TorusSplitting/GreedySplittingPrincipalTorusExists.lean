module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsBasisSpanEqOfDiscrete
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.PrincipalTorusEqZeroOfImLattice
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsShortIndependentIsU
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsShortIntegersSpan
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ThickSplitRealSpanBot
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.DivSqLeOfForallDivAddSqLe

@[expose] public section

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

theorem greedy_splitting_exists : SplitStatement := by
  intro E _ _ _ X DF P
  by_cases h : X.la1 < P.th
  · exact greedy_splitting_thin exists_short_integers_span
      (exists_short_independent_isU transference_discrete_lattice principalTorus_im_perfect)
      E X DF P h
  · exact ⟨⊥, thickSplit_bot E X DF P h⟩

end GlobalTheory

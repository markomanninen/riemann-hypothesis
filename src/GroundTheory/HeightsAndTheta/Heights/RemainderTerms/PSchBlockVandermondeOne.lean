module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem SchBlockVandermondeOne.proof : SchBlockVandermondeOne.Statement := by
  intro N
  simp only [blockVandermonde, vandermondeOf, Fin.prod_univ_one, map_prod, map_sub, rename_X]

end GroundTheory.Heights₂.Heights.RestTerms

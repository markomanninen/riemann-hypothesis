module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarOfInvariantRadonOnCosetsStatement

@[expose] public section

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory

theorem normaliseGroupClause_holds : NormaliseGroupClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH _ _ ν _ μ hμ
  exact GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets G H hH ν μ hμ

end GlobalTheory

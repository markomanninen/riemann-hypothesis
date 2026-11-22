module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChebotarevDegreeOneValuationSubrings
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModChebOm

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chebotarev_degreeOne_valuationSubrings : ReciprocityTheory.ChartRestriction.L1.ChebOmSt := by
  first | exact @GlobalTheory.chebOmSt_holds | exact GlobalTheory.chebOmSt_holds | (intros; apply GlobalTheory.chebOmSt_holds <;> assumption)

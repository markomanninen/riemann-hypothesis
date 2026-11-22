module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyHypothesesOfWorkingClassSevenDutiesStatement
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop

namespace GlobalTheory.Fc.Ind

def lowScalarPt (C CH : ℝ) : PtP := fun _ _ _ p => (p.S true).L6 (p.N C CH)

end GlobalTheory.Fc.Ind

end

module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResInjOfDetermined
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypesStatement

@[expose] public section

noncomputable section

namespace GlobalTheory.LowTypeRestriction

theorem determinedByLowTypes : DeterminedByLowTypes := GlobalTheory.T.multiplicitySpace_eq_zero_of_lowestKTypes

theorem resInj : GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt.ResInj := resInj_of_determined determinedByLowTypes

end GlobalTheory.LowTypeRestriction

end

module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFacts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.RenameTauHomogB

@[expose] public section

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

theorem stable_complement_exists : StableCompl := stableCompl_B

theorem highest_weight_vector_exists : HighestVec := highestVec_B

end PI.WGB

module

public import Mathlib
public import GroundTheory.LocalFields.LocalFourierExistence
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.Assembly

@[expose] public section

namespace PositivityTheory.PfBern.Props1

open PositivityTheory.PfBern.Assembly

theorem existsAddChar_holds : ExistsAddChar := fun k _ _ _ _ =>
  GroundTheory.LocalField.exists_addChar_continuous_ne_one (K := k)

end PositivityTheory.PfBern.Props1

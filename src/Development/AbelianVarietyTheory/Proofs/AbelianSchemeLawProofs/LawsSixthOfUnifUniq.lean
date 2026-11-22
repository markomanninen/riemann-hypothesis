module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUniqueStatement

@[expose] public section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem lawsSixth_of_unifUniq : GlobalFnsSt → SecBaseChangeSt → AmpleSt → Laws6 :=
  fun h₁ h₂ h₃ => ⟨GlobalTheory.T.uniformisation_degenerationData_unique h₁ h₂ h₃⟩

end GlobalTheory

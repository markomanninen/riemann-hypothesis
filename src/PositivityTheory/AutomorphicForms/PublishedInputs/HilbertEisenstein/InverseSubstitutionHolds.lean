module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HcToIdele
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SecondCountableTopologyUnits

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

theorem inverse_substitution_holds : InvSubst := by
  intro F _ _ v f t
  exact MultiplicativeHaarInverse.inv_subst f t

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

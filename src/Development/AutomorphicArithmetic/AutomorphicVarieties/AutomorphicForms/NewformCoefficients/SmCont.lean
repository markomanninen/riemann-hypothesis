module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinSmoothContinuous

@[expose] public section

theorem UpperTheory.V.Af.Nf.smCont :
    UpperTheory.V.Af.Nf.SmCont :=
  UpperTheory.eisenstein_smooth_continuous

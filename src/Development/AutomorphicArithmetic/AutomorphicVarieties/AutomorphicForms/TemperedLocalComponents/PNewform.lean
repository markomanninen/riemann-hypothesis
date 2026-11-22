module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformRepOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PCuspSS
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ExistsContRep

@[expose] public section

open NumberField GlobalTheory.CuspRep UpperTheory.V

theorem UpperTheory.V.Af.newformRep :
    UpperTheory.V.Published.NewformRep :=
  UpperTheory.V.Af.newformRepOf UpperTheory.V.Af.cuspSemisimpleReal UpperTheory.V.Af.admissibleReal

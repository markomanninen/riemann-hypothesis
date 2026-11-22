module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FillPre
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.FrameEx

@[expose] public section

theorem UpperTheory.BaseChangeIdentities.baseChangeN : PositivityTheory.Rg.BcN.BaseChangeIsobaricN :=
  UpperTheory.BaseChangeIdentities.baseChangeN_of UpperTheory.HeckeLevelFrameExistence.candFin

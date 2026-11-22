module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinGCls
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinGTest
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinGStab

@[expose] public section

theorem UpperTheory.V.Z.Sym.Glob.finG :
    UpperTheory.V.Z.Sym.Glob.FinG := by
  intro F _ _ Δ D hD V _ _ ch B s hB
  haveI := hD.real
  refine ⟨⟨?_, finG_stab' hD hB⟩, finG_test hD hB⟩
  rw [hB.U]
  exact finG_cls_of hD B.ι (finG_cls hD.neg B.ι hB.ι)

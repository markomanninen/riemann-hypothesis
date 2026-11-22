module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicFlowMajorantCauchySchwarz
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt

@[expose] public section

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlow_majorant_cauchySchwarz : FlowMajSt := by
  first | exact @GlobalTheory.CuspFrom.flowMajSt_holds | exact GlobalTheory.CuspFrom.flowMajSt_holds | (intros; apply GlobalTheory.CuspFrom.flowMajSt_holds <;> assumption)

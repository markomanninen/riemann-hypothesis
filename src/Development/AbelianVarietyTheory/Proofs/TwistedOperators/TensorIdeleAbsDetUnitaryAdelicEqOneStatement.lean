module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIdeleAbsDetUnitaryAdelicEqOne
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PhaseApply

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorIdeleAbs_det_unitaryAdelic_eq_one : ∀ (D : D7) (W : HSp D) (h : GA D W), GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (matHom W h)) = 1 := by
  first | exact @GlobalTheory.UnitaryDetAbs.absE_det_matHom | exact GlobalTheory.UnitaryDetAbs.absE_det_matHom | (intros; apply GlobalTheory.UnitaryDetAbs.absE_det_matHom <;> assumption)

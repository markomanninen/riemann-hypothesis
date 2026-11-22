module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.Assembly
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.PolyExt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.TorusEigenvalueFormula
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.ModelMap
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.DetSplit
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwIrred

@[expose] public section

theorem modelIso_of : PI.PolyCoef → PI.UnitaryDense → PI.HwIrred → PI.ModelIso :=
  fun hp hu hh => PI.WMI.modelIso_of_steps (PI.WMI.polyExt_of hp hu) PI.WMI.lambda_integrality
    PI.WMI.torus_eigenvalue_formula PI.WMI.lower_triangular_invariance PI.WMI.model_map_equivariance PI.WMI.determinant_splitting_formula hh

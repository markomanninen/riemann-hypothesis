module

public import Mathlib
public import Formalism.PeriodIntegrals.FinOrdAd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicFiniteOrder.Assembly
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitKron
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PowBddInt
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TensCpctDen
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DefPosDef

@[expose] public section

theorem finite_order_adelic : PI.FinOrdAd :=
  PI.finOrdAd_of unit_kronecker power_bounded_integral tensor_compact_dense positive_definite_form

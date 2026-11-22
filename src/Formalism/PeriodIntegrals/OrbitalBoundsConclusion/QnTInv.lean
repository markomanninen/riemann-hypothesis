module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorusInvariance.QnTInvOf
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnMinorLeft
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnEabPres
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnEabGl
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovLin
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovDet
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovHat
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CovariantHatSqOfLin

@[expose] public section

theorem qnTInv : Formalism.FourierDecayAlt.Q.TInvariant :=
  Formalism.FourierDecayAlt.Q.TInvW.qnTInv_of
    (PI.contractionsCovariant_iff.2
      ⟨covariant_det_of_lin covariant_linear, covariant_hat_of_lin covariant_linear, covariant_hat_sq_of_lin covariant_linear⟩)
    qnEabPres qnEabGl qnMinorLeft

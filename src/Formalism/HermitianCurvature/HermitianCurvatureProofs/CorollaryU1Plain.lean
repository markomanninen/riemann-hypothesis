module

public import Formalism.HermitianCurvature.StatementU
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UsCompose
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CutoffPlainAndSmoothed
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UsCost

@[expose] public section

theorem Formalism.FourierDecayAlt.P.corollary_u1_truncated_alt : Formalism.FourierDecayAlt.U.StarBoundOfTwoCutoffOperator :=
  cutoff_plain_and_smoothed.2

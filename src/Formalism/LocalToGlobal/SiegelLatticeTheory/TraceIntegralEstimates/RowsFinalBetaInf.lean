module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BetaInfCoefNZ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.SchurH

@[expose] public section

namespace Formalism.MainNotions.S.Pv.BetaCut

theorem betaInfCoef_ne_zero : BetaInfCoefNZ := PI.BICNZ.betaInfCoefNZ_proof_of PI.WBL.NIS.schurH

end Formalism.MainNotions.S.Pv.BetaCut

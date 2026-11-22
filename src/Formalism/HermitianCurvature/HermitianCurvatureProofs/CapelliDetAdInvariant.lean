module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapAdInv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CvRhoOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SandwichRhoAction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothWordsAll

@[expose] public section

theorem Formalism.FourierDecayAlt.P.capelli_rho_commute : Formalism.FourierDecayAlt.JF.CVRho := by
  exact Formalism.FourierDecayAlt.P.JFxE.cVRho

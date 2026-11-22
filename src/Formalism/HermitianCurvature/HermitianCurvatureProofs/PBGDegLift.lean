module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightAverageSmoothComm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower

@[expose] public section

theorem Formalism.FourierDecayAlt.P.degree_of_lift_pairing : Formalism.FourierDecayAlt.KB.DegLift :=
  Formalism.FourierDecayAlt.P.PBG.degLift_of_parts Formalism.FourierDecayAlt.P.left_fubini_normalized_tower Formalism.FourierDecayAlt.P.PBG.right_average_smooth_comm

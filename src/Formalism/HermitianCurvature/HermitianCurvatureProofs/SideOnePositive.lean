module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Side1PosOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothTruncationInduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LettersPassPartialBessel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Side0PosOf

@[expose] public section

noncomputable section

namespace Formalism.FourierDecayAlt.P

theorem side_one_positive : CutHB.Side1Pos :=
  LevelPointCoordinates.side1Pos_of smooth_truncation_induction smooth_truncation_exists (SliceIntegralLemmas.side0Pos_of'' proper_left_variables_domain)
    letters_pass_partial_bessel proper_left_variables_domain

end Formalism.FourierDecayAlt.P

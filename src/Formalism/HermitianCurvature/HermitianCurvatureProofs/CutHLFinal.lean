module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadLetterOfMinusPos
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLMinusPosOfParts

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutHL

theorem head_letter_of_minus_positive : LevelPointCoordinates.HeadLetter :=
  headLetter_of_minusPos Formalism.FourierDecayAlt.P.minus_positive_of_parts

end Formalism.FourierDecayAlt.P.CutHL

theorem Formalism.FourierDecayAlt.P.head_letter_identity : Formalism.FourierDecayAlt.P.LevelPointCoordinates.HeadLetter := Formalism.FourierDecayAlt.P.CutHL.head_letter_of_minus_positive

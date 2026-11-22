module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLNf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLFrozen

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutHL

theorem headLetter_of_rest (hL : LeftActionRuleAtBasePoint) (hT : TorusDirectionAtBasePoint) (hSL : ConjugateActionRuleAtBasePoint) (hST : ConjugateTorusDirectionAtBasePoint)
    (hPP : PlusPosOfParts) (hPZ : PlusZeroOfParts) (hMP : MinusPosOfParts) (hMZ : MinusZeroOfParts) :
    LevelPointCoordinates.HeadLetter :=
  headLetter_of_open hL hT hSL hST frozen_X_identity frozen_V_identity hPP hPZ hMP hMZ

end Formalism.FourierDecayAlt.P.CutHL

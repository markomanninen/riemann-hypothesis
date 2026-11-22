module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersRealPlacesStatement

@[expose] public section

open Formalism.BasicNotions

namespace GlobalTheory

theorem vacChar_of_record : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D :=
  GlobalTheory.T.thetaVacuumCharacters_realPlaces

end GlobalTheory

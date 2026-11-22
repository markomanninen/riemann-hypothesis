module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VacuumFockVectors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionsSquareIntegrableHeisenbergUnitary

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumFockLaws

theorem vacuumFock_onObjects : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D :=
  fun D => vacuumFock_of_thetaSquareIntegrable D (GlobalTheory.ThetaSquare.thetaFunctions_squareIntegrable_heisenbergUnitary D)

end GlobalTheory.VacuumFockLaws

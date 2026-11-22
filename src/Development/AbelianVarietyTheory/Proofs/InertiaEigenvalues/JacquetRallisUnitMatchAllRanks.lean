module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchOfWeilRepQuadraticStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationQuadraticFieldExistsStatement

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem unitMatch_all : ∀ r, UnitMatch r :=
  GlobalTheory.T.jacquetRallisUnitMatch_of_weilRep_quadratic GlobalTheory.T.weilRepresentation_quadraticField_exists

end GlobalTheory.JR

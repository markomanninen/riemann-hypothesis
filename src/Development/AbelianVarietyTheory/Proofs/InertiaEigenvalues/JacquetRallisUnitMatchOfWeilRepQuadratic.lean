module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchingOfWeilFieldStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSuccStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSizeOneStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilConstantStandardHermitianEqOneStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationEtaleOfQuadraticFieldStatement

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem unitMatch_of_weilField : WeilField → ∀ r, UnitMatch r := by
  intro hW r
  induction r with
  | zero => exact GlobalTheory.T.jacquetRallisUnitMatch_sizeOne
  | succ r ih => exact GlobalTheory.T.jacquetRallisUnitMatch_succ (GlobalTheory.T.weilRepresentationEtale_of_quadraticField hW) GlobalTheory.T.weilConstantStandardHermitian_eq_one r (GlobalTheory.T.jacquetRallis_fourier_matching_of_weil_field hW (r + 1)) ih

end GlobalTheory.JR

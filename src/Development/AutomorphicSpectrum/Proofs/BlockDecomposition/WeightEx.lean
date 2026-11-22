module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.GalStepOfHyp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicWeightOfAutomorphicDefiniteUnitarStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAtStatement

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.WeightExist

theorem weightEx : PositivityTheory.Rg.BcB.F.WeightEx :=
  fun E _ _ _ n π hπ τ => (GlobalTheory.T.existsUnique_weight_definiteUnitary_at E n (GlobalTheory.DefU.AU.mk ⟨π, hπ⟩) τ).exists

end GlobalTheory.CompanionTheory.WeightExist

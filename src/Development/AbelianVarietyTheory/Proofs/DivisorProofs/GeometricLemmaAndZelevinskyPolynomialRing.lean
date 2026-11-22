module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltration
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskyGrothendieckPolynomialRingOfSegments
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BzfinHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaFiltrationUnconditional
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SegmentRepresentation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GrothendieckRingPolynomialOutright

@[expose] public section

namespace GlobalTheory

theorem geometricLemma_and_zelevinskyPolynomialRing :
    GlobalTheory.Published.GeometricLemma ∧ GlobalTheory.Published.ZelevinskyPolynomialRing :=
  ⟨GlobalTheory.geometricLemma_of_filtration GlobalTheory.Laid.bzfin_holds
               GlobalTheory.geometricLemmaFiltration_unconditional,
    GlobalTheory.zelevinskyPolynomialRing_of_parts GlobalTheory.Laid.bzfin_holds
      GlobalTheory.segmentRepresentation' GlobalTheory.grothendieckRingPolynomial_outright⟩

end GlobalTheory

module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormSub
public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesFiniteClassDecomposition
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowNormOneIdeleEqPrincipalMulIntegralUnit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitsFinitelyManyNorms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugacyClassClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitsLocallyCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCentralizerTranslate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryPointsAtPlaceFstMemCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOrbitCentralizerAlmostAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdelicPointOfEventuallyIntegralLocaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointExtOfComponentsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryAdelicProdLocalCompactsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompactUnitaryAdelicImageIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryAdelicComponentAtPlaceExplicitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralUnitaryPointsAtPlaceMulMemStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactIntegralUnitaryPointsAtPlaceStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.MapInclKMemTwCentResOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigResIterateEqSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigIterateApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFrStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatesSeparableMatrixCompactModCentralizer
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC
public import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.CycFieldA
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsB
public import Development.AbelianVarietyTheory.Definitions.Divisors.ShiftTw
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFr
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerRegularRationalPointFiniteAdelicComm
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtA
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedSimilitudePairMinpolyRootsNormSqEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousFiniteAdeleEquivRatIntStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousRestrStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFiniteAdelesSplitAwayFromPrimePadicStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitIdempotentConjugation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerBasisOfCharpolySeparable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCentralizerRegularTwistedCentraliserStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairRegularImageAtPStatement

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.CentTorus.AdelicSplit

section Tmap

variable {A B L : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B] [CommRing L] [Algebra ℚ L]

end Tmap

end GlobalTheory.CentTorus.AdelicSplit

namespace GlobalTheory.CentTorus.AdelicSplit

end GlobalTheory.CentTorus.AdelicSplit

namespace GlobalTheory.CentTorus.AdelicSplit

theorem adele_split (p : ℕ) [Fact p.Prime] :
    ∃ (π₁ : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] AfP p) (π₂ : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] ℚ_[p]),
      Continuous π₁ ∧ Continuous π₂ ∧ Function.Bijective (fun a => (π₁ a, π₂ a)) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_continuous_finiteAdele_equiv_rat_int
  obtain ⟨π, hπc, hπb⟩ := GlobalTheory.T.ratFiniteAdeles_split_awayFromPrime_padic p
  let r : FiniteAdeleRing ℤ ℚ →ₐ[ℚ] AfP p := { AfP.restr p with commutes' := fun _ => rfl }
  exact ⟨r.comp e.toAlgHom, π.comp e.toAlgHom, (GlobalTheory.T.continuous_afP_restr p).comp he, hπc.comp he, hπb.comp e.bijective⟩

end GlobalTheory.CentTorus.AdelicSplit

section Final

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.CentTorus
open scoped TensorProduct Classical

end Final

module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuadraticPowerCharacterSplitPlacesValuesInverse
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits

@[expose] public section

noncomputable section

namespace GlobalTheory.UnrEuler.ConjFac

open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors TensorProduct
open Formalism.L2.Host (aboveF)
open GlobalTheory.CuspRep (conjSrc conjPl_conjSrc)

theorem absNorm_conjSrc {E : Type} [Field E] [NumberField E] (c : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm (conjSrc c w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc c w)]
  rw [Ideal.absNorm_eq_natCard, Ideal.absNorm_eq_natCard]
  exact Nat.card_congr (Ideal.quotientEquiv (w.asIdeal.comap (RingOfIntegers.mapRingEquiv c)) w.asIdeal
    (RingOfIntegers.mapRingEquiv c)
    (Ideal.map_comap_of_surjective _ (RingEquiv.surjective (RingOfIntegers.mapRingEquiv c)) _).symm).toEquiv

end GlobalTheory.UnrEuler.ConjFac

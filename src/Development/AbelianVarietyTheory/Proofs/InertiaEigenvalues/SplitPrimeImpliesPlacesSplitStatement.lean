module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimeImpliesPlacesSplit
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.SplitRowIffOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_prime_implies_places_split : ∀ {R : Ranks} (H : Host R) (l : ℕ), SplitRowPrime H l → PlacesSplit H l := by
  first | exact @GlobalTheory.SplitPlaces.placesSplit | exact GlobalTheory.SplitPlaces.placesSplit | (intros; apply GlobalTheory.SplitPlaces.placesSplit <;> assumption)

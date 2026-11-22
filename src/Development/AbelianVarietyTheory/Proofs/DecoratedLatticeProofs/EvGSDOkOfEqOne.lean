module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
public import Formalism.LocalToGlobal.Columns.ToHLat
public import Formalism.HarderNarasimhan.QuotRealize
public import Formalism.LocalRingCardinality.DataArith
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows

@[expose] public section

noncomputable section

namespace GlobalTheory.CoreHt

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds

theorem evGSD_ok_of_eq_one : ∀ (X : Fields) [_root_.NumberField.IsTotallyComplex X.K] (hX : X.Ok) (Pr : Primes X) (R : Ranks)
    (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg)
    (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word), Pr.Ok → mu = 1 → (evGSD W Ch sel mu P u).Ok := by
  intro X _ hX Pr R W Ch sel Sg mu P u hPr hmu
  subst hmu
  exact GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.evOk W Ch sel Sg hX hPr P u

end GlobalTheory.CoreHt

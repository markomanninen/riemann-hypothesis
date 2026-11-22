module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsTheRecOfIsRecLit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuationStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportIrrGLBijectiveDegreeCharZeroStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsCuspidalTwistsCharactersStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsDataTransportLocalFieldIsoStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymmStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinMapUniqueTransportPlaceIsoStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsCuspidalTwistsCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientComp

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.LocLanglands.FieldCompat GlobalTheory.LocLanglands.TransportGL GlobalTheory.TheRecTransport

namespace GlobalTheory.LawsTTransport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}

theorem eig_of_wdRel {φ : Ω ≃+* Ω'} {y : WD h} {y' : WD h'} (H : WDRel φ y y') {σ : Weil h} {σ' : Weil h'}
    (hσ : WeilRel φ σ σ') : y.eig σ = y'.eig σ' := by
  obtain ⟨n, b, b', e1, e2, -, hb⟩ := H
  rw [← e1, ← e2, WD.eig, WD.eig, WD.charPol_mk, WD.charPol_mk, hb σ _ hσ]

end GlobalTheory.LawsTTransport

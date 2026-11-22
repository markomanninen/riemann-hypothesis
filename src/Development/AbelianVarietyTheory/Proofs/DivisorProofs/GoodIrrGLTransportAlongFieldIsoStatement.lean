module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIrrGLTransportAlongFieldIso
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_irrGL_transport_along_fieldIso : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (x : IrrGL (k := k)) (x' : IrrGL (k := k')), RepRel i x x' → UpperTheory.Zero.LLC.Good x → UpperTheory.Zero.LLC.Good x' := by
  first | (exact @GlobalTheory.RecTTransport.good_of_repRel) | (exact GlobalTheory.RecTTransport.good_of_repRel) | (intros; apply GlobalTheory.RecTTransport.good_of_repRel  <;> assumption)

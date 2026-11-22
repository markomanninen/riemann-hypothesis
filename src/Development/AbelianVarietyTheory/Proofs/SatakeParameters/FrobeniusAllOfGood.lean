module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadLift
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfiniteQuadraticCMGoodBaseChangeSplitStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRestStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeightStatement
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RamificationIdxEqOneAndInertiaDegEqOne
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.BridgeJMemKwOfDecLe
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.DRSstCrysPstJumpsDescend
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.WdRelOfFrobSS
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExBridge
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymmStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GamGalEqOfPlaceIso

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.PhiDescent

theorem wdRel_trivWD {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (a : ℕ) :
    WDRel φ (trivWD h a) (trivWD h' a) := by
  refine ⟨a, WDRep.diag h fun _ : Fin a => 1, WDRep.diag h' fun _ : Fin a => 1, rfl, rfl, ?_, ?_⟩
  · rfl
  · intro σ σ' _
    ext v i
    simp [WDRep.diag, WDRep.ofChars, GlobalTheory.WeilDeligne.unrChar]

theorem charPol_eq {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
    {φ : Ω ≃+* Ω'} {y : WD h} {y' : WD h'} (hy : WDRel φ y y') {σ : Weil h} {σ' : Weil h'} (hs : WeilRel φ σ σ') :
    y.charPol σ = y'.charPol σ' := by
  obtain ⟨n, b, b', rfl, rfl, -, hb⟩ := hy
  rw [WD.charPol_mk, WD.charPol_mk, hb σ σ' hs]

end GlobalTheory.RoadU.PhiDescent


end

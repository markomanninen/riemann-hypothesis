module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TemperedProductOfSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BrauerDegreeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissible
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiTempered
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeakRepIso
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.WignerVanishingGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.LocalGlobalAboveL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColRepSemisimple
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InvTransposeInvTranspose
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivContraLocComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjOpInvolutive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilRepEquivOfCharpolyEq
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RecAlgNormDiag
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.WeakTheRep

theorem eq_of_mono0_charPol {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (x y : WD h)
    (hx : x.mono0) (hy : y.mono0) (hc : ∀ g, x.charPol g = y.charPol g) : x = y := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  obtain ⟨m, b, rfl⟩ := WD.exists_rep y
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at hx hy
  obtain ⟨e, he⟩ := GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq E Ω A w h n m a b
    (fun σ => by rw [← WD.charPol_mk, ← WD.charPol_mk]; exact hc σ)
  exact WD.sound ⟨e, he, fun v => by rw [hx, hy]; simp⟩

theorem fixed_ne_bot_of_equiv {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} (e : ρ.Equiv ρ') {K : Subgroup G}
    (h : GlobalTheory.PRep.fixed ρ K ≠ ⊥) : GlobalTheory.PRep.fixed ρ' K ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨e v, ?_, fun h0 => hv0 ?_⟩
  · refine GlobalTheory.ContraRefl.mem_fix.2 fun g hg => ?_
    have h1 := LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) v
    simp only [LinearMap.comp_apply] at h1
    rw [GlobalTheory.ContraRefl.mem_fix.1 hv g hg] at h1
    exact h1.symm
  · exact e.toLinearEquiv.injective (h0.trans (map_zero e.toLinearEquiv).symm)

end GlobalTheory.WeakTheRep

end

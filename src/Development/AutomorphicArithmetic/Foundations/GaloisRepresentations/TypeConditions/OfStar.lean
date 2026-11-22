module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjBis
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.PowEqOneOfRoots
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.InePolOfUnr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConj
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspContragredientIsCMConjTwistOfPairedInvTranspStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalOfGelfandKazhdan
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfRegularAlgebraicPolarizedPStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopStd
public import Development.AutomorphicArithmetic.NaturalDivisibility.ExistsContinuousRingEquivPadicOfTotallySplit

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.GalStar
open scoped commutatorElement

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalS

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem star_guard {y : WD h} (k : NcW y) : (IsQpBig w y.lpDim ∧ TmW y ∧ UpperTheory.GalStar.Sqf y) ∨ Tor y := by
  by_cases hs : ∃ p : ℕ, p.Prime ∧ w ∈ placesOver E p ∧ (placesOver E p).ncard = Module.finrank ℚ E ∧
      (y.lpDim = 1 ∨ 16 * y.lpDim ^ 2 < p)
  · have ht : thr w y.lpDim = 2 := if_pos hs
    obtain ⟨p, hp, hw, hc, hb⟩ := hs
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨i, hi⟩ := UpperTheory.exists_continuous_ringEquiv_padic_of_totally_split E w p hw hc
    exact Or.inl ⟨⟨p, inferInstance, i, hi, hb⟩, k.1, fun γ hγ hg z hz => k.2.2 γ hγ hg z (by rwa [ht])⟩
  · exact Or.inr (tor_of_ncW (if_neg hs) k)

theorem tor_of_unr {y : WD h} (u : y.unr) : Tor y := fun s t => by
  have hd : deg ⁅s, t⁆ = 0 := by simp [commutatorElement_def]
  have := inePol_of_unr u (deg_eq_zero_iff.1 hd)
  rwa [WD.inePol_of_mem _ (⁅s, t⁆ : ↥(Weil h)).2] at this

theorem away_nice {x y : WD h} (a : AwayB x y) (k : NcW y) :
    x.mono0 ∧ ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g := by
  rcases star_guard k with ⟨q, t, s⟩ | t
  · exact a.tame0 q t s k.2.1
  · rw [a.tor t k.2.1]; exact ⟨k.2.1, fun _ _ => rfl⟩

theorem aw_of_away {x y : WD h} (a : AwayB x y) : Aw x y :=
  ⟨a.dim, fun u => a.tor (tor_of_unr u) (WD.unr_mono0 _ u), fun k => (away_nice a k).2, fun k => (away_nice a k).1⟩
end

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]


end UpperTheory.GalS

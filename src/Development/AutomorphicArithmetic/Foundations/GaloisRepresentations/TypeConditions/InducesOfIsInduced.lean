module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOfSamePlace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm2OfHyp
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleOfRankOneUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystalline
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.UnrRecOfHasSat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.InePolOfUnr

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalS.Prod

open GlobalTheory GlobalTheory.GalFirstClause Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp GlobalTheory.HeckeGal

theorem norm_algHom {l : ℕ} [Fact l.Prime] {K L : FinExt l} (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (y : ↥K.1) :
    ‖((τ y : ↥L.1) : Om l)‖ = ‖(y : Om l)‖ := by
  have e1 : minpoly ℚ_[l] ((τ y : ↥L.1) : Om l) = minpoly ℚ_[l] y :=
    minpoly.algHom_eq (L.1.val.comp τ) (L.1.val.comp τ).toRingHom.injective y
  have e2 : minpoly ℚ_[l] (y : Om l) = minpoly ℚ_[l] y := minpoly.algHom_eq K.1.val K.1.val.toRingHom.injective y
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm, e1, e2]

theorem induces_of_isInduced {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Bw : LocBridge l E Ω (Dec (F := E) A) O}
    (hj : Induces Bw) {τ : E →+* Om l} {LL' : FinExt l} {τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1} (hτ : IsInduced Bw τ τ')
    (x : 𝓞 E) : ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal := by
  rw [hτ, norm_algHom]
  exact (hj.valuation_lt_one_iff _).symm.trans (h x)


end UpperTheory.GalS.Prod

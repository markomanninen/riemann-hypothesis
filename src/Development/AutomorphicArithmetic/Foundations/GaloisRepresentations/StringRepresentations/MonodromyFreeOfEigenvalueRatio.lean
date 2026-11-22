module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.WeightsConj
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilRepEquivOfCharpolyEq
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PstAndWdAtOfIsRegAlg
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleOfRankOneUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOfSamePlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleWdEigenEqualNorm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedDirectSum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace UpperTheory.GalN

section Lin
variable {V : Type} [AddCommGroup V] [Module ℂ V]

end Lin

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

def EV (a : WDRep h V) (χ : ↥(Ine (F := E) A) → ℂ) (v : V) : Prop := ∀ s, a.ρ (ineIncl h s) v = χ s • v

def Win (a : WDRep h V) (S : Set ℝ) : Prop :=
  ∀ χ, (∀ v, EV a χ v → a.N v = 0) → ∀ r v, EV a χ v → v ∈ absSpace (a.ρ (frob h)) r → v ≠ 0 → r ∈ S

end UpperTheory.GalN

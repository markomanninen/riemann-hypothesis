module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.FrobOfProps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolvableEquivalenceOfBaseChange
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ExistenceOfGaloisRepresentationsOfHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.DenseRangeUnitsR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AutBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SelfTwGal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicCharConjInvariant
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicCharacterPlusPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicSolutionParallel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SignAtInfinityOfParallelWeight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisCharacterFrobeniusCompatibility
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeEigenvalueBasicProperties
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.NormCharacterOfFrobeniusCompatibility
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteCharacterOfAlgebraicCyclotomic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CharacterExtendsToGaloisGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusDualityComplexConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ComplexConjPlaceUnderEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DualBaseChangeOfFrobeniusDualityOfConjUnder
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusConjOfGaloisConjugatePlaces
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeInvariantOfFrobConjOfEigenvalueBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeBaseChangeAttached
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SemisimpleModuleRestrictionToNormalSubgroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SchurExtension
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepresentationIrreduciblePrimeDimension
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepresentationImageSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SolvableCyclicSubextensionOverRat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SolvableAuxiliaryGaloisExtension
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SolvableCmCompositumMaximalRealSubfield
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SolvableCmExtensionTower
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SolvablePolarizedRestriction
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ExistenceOfGaloisRepresentationsOfHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc UpperTheory.V.Af.Sol

namespace UpperTheory.V.Z.Bc

private theorem cusp_unique {F : Type} [Field F] [NumberField F] {n : ℕ} {sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop}
    {inf : (F →+* ℂ) → Multiset ℂ → Prop} (h : IsCusp n sat inf) : ∀ v B B', sat v B → sat v B' → B = B' := by
  rcases h with ⟨_, π, rfl, -⟩ | ⟨_, π, rfl, -⟩
  · exact fun _ _ _ h h' => h.unique h'
  · exact fun _ _ _ h h' => h.unique h'

private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

end UpperTheory.V.Z.Bc

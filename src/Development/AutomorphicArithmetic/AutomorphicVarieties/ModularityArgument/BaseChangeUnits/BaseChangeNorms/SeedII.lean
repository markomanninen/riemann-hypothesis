module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadraticInductionGL2Alt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricSquareMixedExists
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ContinuousMixFamily
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsSquareRootOfCharacterNearOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticCharacterOfSubgroupIndexTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepPropertiesInvariantUnderConjugation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRibetLattice
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisCharacterResidualDecomposition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InducedIrreducible
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InducedFinalStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.IndGlobOfKill
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InducedRepresentationConstituentVanishing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InducedFlagCondition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InducedDeletionCondition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InertiaActsTriviallyOnRootsOfUnity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.IrrIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ShapeFacts

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

section

variable {l : ℕ} [Fact l.Prime]

private theorem norm_of_cong {a b : Qbar l} (h : ‖a - b‖ < 1) (hb : ‖b‖ = 1) : ‖a‖ = 1 := by
  have e : a = (a - b) + b := by ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hb]; exact h.ne), hb, max_eq_right h.le]

end

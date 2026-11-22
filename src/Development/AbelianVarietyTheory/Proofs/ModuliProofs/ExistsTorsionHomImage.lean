module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePairIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OverExtOfPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionToG
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartImageGeneric
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartImagePullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SameUnifRefl
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndFlatMulAbelianSchemeStatement
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPtsEquiv
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsRepMap

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorsionFormCompare GlobalTheory.TorusModel GlobalTheory.FieldRestrictionTest

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

variable {Gt : Over (Sp R)} [GrpObj Gt] {Φ : ∀ T, (T ⟶ Gt) ≃ GtPt D T}

end Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)}

end GlobalTheory.TorsRepMap

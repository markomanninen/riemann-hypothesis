module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecIsMulOfBaseMultipleThetaSection
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secIsMul_of_baseMultiple_thetaSection : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (th g : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (b : R), GlobalTheory.PsiRing.Mult D th g b → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom b g th := by
  first | exact @GlobalTheory.PsiRing.secIsMul_of_mult | exact GlobalTheory.PsiRing.secIsMul_of_mult | (intros; apply GlobalTheory.PsiRing.secIsMul_of_mult <;> assumption)

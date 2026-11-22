module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonvanishingOfInvertiblePushforward
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
theorem _root_.GlobalTheory.T.fibrewise_nonvanishing_of_invertible_pushforward : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t₀ : SAB H S), PushInvertible t₀.G t₀.PP.L → ∀ (R : Type) [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ S) (t : SAB H (Sp R)) (_ : SABMap t t₀ ξ), ThetaNZ t.G t.PP.L := by
  first | exact @GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible | exact GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible | (intros; apply GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible <;> assumption)

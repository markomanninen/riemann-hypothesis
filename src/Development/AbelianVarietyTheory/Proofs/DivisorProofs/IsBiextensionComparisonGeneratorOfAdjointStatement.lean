module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBiextensionComparisonGeneratorOfAdjoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBiextensionComparisonGenerator_of_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₀ : DegPre R) (q : D.P.A ⟶ D₀.P.A) (j : D₀.P.A ⟶ D.P.A), IsMonHom q → IsMonHom j → AdjCls (cls D.P.L D.P.isLB) (cls D₀.P.L D₀.P.isLB) q j → CmpTwo D D₀ q j := by
  first | exact @GlobalTheory.Mum.PowData.cmpTwo_of_adjCls | exact GlobalTheory.Mum.PowData.cmpTwo_of_adjCls | (intros; apply GlobalTheory.Mum.PowData.cmpTwo_of_adjCls <;> assumption)

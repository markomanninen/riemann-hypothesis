module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
public import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.KeyCancel

theorem keyPB_id_of_keyPB : ∀ (R K : Type) [CommRing R] [Field K] (f : R →+* K) (x : KeyIn R) (x₁ x₂ : KeyIn K), KeyPB x₁ x f → KeyPB x₂ x f → KeyPB x₁ x₂ (RingHom.id K) :=
  fun R K _ _ f x x₁ x₂ h₁ h₂ =>
    keyPB_cancel R K K x x₂ x₁ f (RingHom.id K) h₂ (by rwa [RingHom.id_comp])

end GlobalTheory.KeyCancel

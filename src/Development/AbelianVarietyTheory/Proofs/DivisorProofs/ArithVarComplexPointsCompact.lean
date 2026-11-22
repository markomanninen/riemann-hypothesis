module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictChernPart
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero

@[expose] public section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier
open ReciprocityTheory.AnForm.M

namespace GlobalTheory

theorem IsArithVar.finite_emb_and_topology : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ}, IsArithVar p D →
    Finite (k →+* ℂ) ∧ ∀ σ : k →+* ℂ, CompactSpace (CxPts p σ) ∧ T2Space (CxPts p σ) ∧
      SecondCountableTopology (CxPts p σ) := fun h =>
  ⟨h.finite_emb, fun σ => ⟨h.compactSpace σ, CxPts.t2Space_cxPts_of_isProjOver σ h.isProjOver,
    CxPts.secondCountableTopology_of_isProjOver σ h.isProjOver⟩⟩

end GlobalTheory

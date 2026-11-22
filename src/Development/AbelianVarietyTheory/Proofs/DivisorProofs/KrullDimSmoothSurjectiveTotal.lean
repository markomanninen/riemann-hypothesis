module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimLeZeroOfSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimFiberStalkEqQuotient

@[expose] public section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false
namespace GlobalTheory.SmoothDimTotal
open IsLocalRing

theorem topologicalKrullDim_eq_iSup_stalk (X : Scheme.{0}) :
    topologicalKrullDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x) := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]
  simp only [ringKrullDim_stalk_eq_coheight]

theorem ringKrullDim_stalk_le_of_smooth (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (.of K)) (n : ℕ)
    (h : SmoothOfRelativeDimension n f) (x : X) : ringKrullDim (X.presheaf.stalk x) ≤ n := by
  haveI : Nonempty X := ⟨x⟩
  rw [ringKrullDim_stalk_eq_coheight, ← GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth f n h]
  exact (Order.coheight_le_krullDim x).trans (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))).ge

end GlobalTheory.SmoothDimTotal

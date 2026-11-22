module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

@[expose] public section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.FlagFamily

open Limits

theorem isProjOver_pullback_over {k : Type} [CommRing k] {B X Y : Scheme.{0}} {q : B ⟶ Sp k} (hq : IsProjOver q)
    {f : X ⟶ B} {g : Y ⟶ B} (hf : IsProjOver (f ≫ q)) (hg : IsProjOver (g ≫ q)) :
    IsProjOver (pullback.fst f g ≫ f ≫ q) := by
  have : IsProper q := projProper k B q hq
  have h := ProjSpace.isProjOver_comp_of_isClosedImmersion (pullback.mapDesc f g q)
    (ProjSpace.isProjOver_pullback hf hg)
  rwa [pullback.lift_fst_assoc, Category.comp_id] at h

end GlobalTheory.FlagFamily

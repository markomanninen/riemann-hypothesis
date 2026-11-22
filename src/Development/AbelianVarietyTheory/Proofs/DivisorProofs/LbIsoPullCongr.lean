module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomDescendsToSubfieldContainingFinset
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LbIsoDescendsToSubfieldContainingFinset
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.CxPts GlobalTheory.Points
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.MBDesc

theorem lbIso_pullComp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (g : Z ⟶ Y) :
    LBIso (L.pull (g ≫ f)) ((L.pull f).pull g) :=
  ClosedPol.lbIso_pull_comp hL f g (g ≫ f) rfl

theorem lbIso_pull_congr {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {f g : Y ⟶ X} (h : f = g) :
    LBIso (L.pull f) (L.pull g) :=
  h ▸ RigidBundleGlue.LBIso.pull (GlobalTheory.lbIso_refl hL) f

end GlobalTheory.MBDesc

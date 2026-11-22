module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectOfCoveringPullbacks
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullLevelObject_of_covering_pullbacks : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lv : D.La → (𝟙_ (Over S) ⟶ t.G)), 0 < N → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ a c, lv (a + c) = lv a * lv c) → (∀ a, lv (N • a) = 1) → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (ν : SABMap t' t f) (lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)), p ∈ Set.range f ∧ (∀ a, (lv' a).left ≫ ν.φ = f ≫ (lv a).left) ∧ FullObj D (f ≫ s) t' lv') → FullObj D s t lv := by
  first | exact @GlobalTheory.FullDescent.fullObj_of_cover | exact GlobalTheory.FullDescent.fullObj_of_cover | (intros; apply GlobalTheory.FullDescent.fullObj_of_cover <;> assumption)

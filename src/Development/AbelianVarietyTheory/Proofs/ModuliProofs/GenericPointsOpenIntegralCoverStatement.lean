module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
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
theorem _root_.GlobalTheory.T.generic_points_open_integral_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (O : Type) [CommRing O] [IsNoetherianRing O] (MM : Scheme.{0}) (sM : MM ⟶ Sp O) (tM : SAB H MM) (m : ℕ), IsReduced MM → LocallyOfFiniteType sM → QuasiCompact sM → (∀ ξ ∈ genericPoints MM, ∃ (V : Scheme.{0}) (i : V ⟶ MM) (tV : SAB H V) (_ : SABMap tV tM i) (C : ZOn (i ≫ sM) tV m), IsOpenImmersion i ∧ ξ ∈ Set.range i ∧ IsIntegral V ∧ IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L (m ^ 2), A.r = r ∧ A.s = 1) → (∃ g, SmoothOfRelativeDimension g tM.G.hom) → Out.Laws → Out.Laws2 → IsProper tM.G.hom → Out.RelAmple tM.G tM.PP.L → Out.KTriv tM.G tM.PP.L → Nonempty (ZOn sM tM m) := by
  first | exact @GlobalTheory.Models.nonempty_zOn_of_components | exact GlobalTheory.Models.nonempty_zOn_of_components | (intros; apply GlobalTheory.Models.nonempty_zOn_of_components <;> assumption)

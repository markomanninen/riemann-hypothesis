module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AmpleDeterminantFramesPullbackOfIsAffineHom
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
theorem _root_.GlobalTheory.T.ampleDeterminantFrames_pullback_of_isAffineHom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z Z' : Scheme.{0}) (t : SAB H Z) (t' : SAB H Z') (f : Z' ⟶ Z) (_ : SABMap t' t f) (N : ℕ) (A : GlobalTheory.LN.AmpFrames t.G t.PP.L N), IsAffineHom f → ∃ A' : GlobalTheory.LN.AmpFrames t'.G t'.PP.L N, A'.r = A.r ∧ A'.s = A.s := by
  first | exact @GlobalTheory.AmpPull.ampFrames_pull_of_isAffineHom | exact GlobalTheory.AmpPull.ampFrames_pull_of_isAffineHom | (intros; apply GlobalTheory.AmpPull.ampFrames_pull_of_isAffineHom <;> assumption)

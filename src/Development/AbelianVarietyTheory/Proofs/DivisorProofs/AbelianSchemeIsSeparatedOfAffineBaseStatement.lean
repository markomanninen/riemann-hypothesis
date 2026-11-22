module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsSeparatedOfAffineBase
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_isSeparated_of_affine_base : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → A.left.IsSeparated := by
  first | exact @GlobalTheory.abelianScheme_left_isSeparated_of_affine | exact GlobalTheory.abelianScheme_left_isSeparated_of_affine | (intros; apply GlobalTheory.abelianScheme_left_isSeparated_of_affine <;> assumption)

module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianO1PullbackFubiniStudyMetric
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemPointIdealIffEvalCoordsZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealHorizontalIffCharZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureDimIffArithmeticVarietyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecializesIffPointIdealLeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectivePrimeEqPointIdeal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointHasNonzeroLift
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTensorProduct
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepDualInverse
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTensorPower
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTrivialLineBundle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepOfIsometric
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepMetricSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTwistedBundleExistsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem dict_ptIdeal_injective {m : ℕ} (n : Fin (m + 1) → ℕ) :
    Function.Injective (ptIdeal : MP ℤ m n → Ideal (Geo.MRing (Bk n))) := fun x y h =>
  (((GlobalTheory.T.specializes_iff_point_ideal_le m n x y).2 h.le).antisymm ((GlobalTheory.T.specializes_iff_point_ideal_le m n y x).2 h.ge)).eq

end GlobalTheory.CompanionTheory.MPDict

module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RationalityOfResolutionStatementStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianLineBundleSmoothStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCyclePointDictionaryStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleCodimensionOneStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleRationalExistsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleOfRationalStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanIntegralEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanIntegrableOnStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsFurther
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPointLengthFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCurveIntersectionFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightEqOfFullIntersectionSystemStatement

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem isArithVar_mpStr (m : ℕ) (n : Fin (m + 1) → ℕ) : GlobalTheory.IsArithVar (mpStr ℤ m n) (∑ i, n i) :=
  GlobalTheory.Amb.isArithVar_mp ℤ inferInstance m n

theorem dim_of_isArithVar (hD : GlobalTheory.CompanionTheory.MixZ.PtDict) {m : ℕ} {n : Fin (m + 1) → ℕ} {Z : Scheme.{0}} [IsIntegral Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] {d : ℕ} (hd : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) d) :
    topologicalKrullDim Z = d := by
  obtain ⟨d', hd'⟩ := (isArithVar_mpStr m n).exists_dim_eq i
  obtain ⟨-, -, h₃, -⟩ := hD m n Z i d' hd'
  have h₄ := h₃ hd.2.2.1
  have e : d' + Fintype.card (Fin (m + 1)) = d + Fintype.card (Fin (m + 1)) := by
    exact_mod_cast h₄.2.2.2.symm.trans hd.2.2.2
  rw [hd', Nat.add_right_cancel e]

end GlobalTheory.CompanionTheory.MPDict

module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DependencyStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dependency_statement : DepSt := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.depSt | exact GlobalTheory.CompanionTheory.FewEq.depSt | (intros; apply GlobalTheory.CompanionTheory.FewEq.depSt <;> assumption)

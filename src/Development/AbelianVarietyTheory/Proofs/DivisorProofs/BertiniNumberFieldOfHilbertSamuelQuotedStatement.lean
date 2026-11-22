module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniNumberFieldOfHilbertSamuel
public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bertiniNumberField_of_hilbertSamuel₂ : Quoted → BertiniNF := by
  first | exact @GlobalTheory.HSShort.bertiniNumberField_of_hilbertSamuel | exact GlobalTheory.HSShort.bertiniNumberField_of_hilbertSamuel | (intros; apply GlobalTheory.HSShort.bertiniNumberField_of_hilbertSamuel <;> assumption)

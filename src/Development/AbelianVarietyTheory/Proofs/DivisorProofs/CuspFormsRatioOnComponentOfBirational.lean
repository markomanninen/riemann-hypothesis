module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearSystemRatioOfDegreeOfGeneratesByRatiosStatement

@[expose] public section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.DegVal

set_option synthInstance.maxHeartbeats 1000000 in
theorem ratioOn_of_birOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), ∀ (Z : Comp Xo c) (G : WTZ E), BirOn U Z G → RatioOn U Z G := by
  intro E _ _ _ H Dw l Xo c r U Z G hB τ t _
  exact GlobalTheory.T.isLinearSystemRatioOfDegree_of_generatesByRatios _ _ _ _ hB τ _

end GlobalTheory.DegVal


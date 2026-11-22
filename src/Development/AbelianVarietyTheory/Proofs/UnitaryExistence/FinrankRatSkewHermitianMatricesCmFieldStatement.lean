module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinrankRatSkewHermitianMatricesCmField
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
public import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_rat_skewHermitian_matrices_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ρ : ℕ) (Ψ : Finset (E →+* ℂ)), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → ∀ W : Submodule ℚ (Matrix (Fin ρ) (Fin ρ) E), (∀ β, β ∈ W ↔ FJ.IsSkew β) → Module.finrank ℚ W = Ψ.card * ρ ^ 2 := by
  first | exact @GlobalTheory.finrank_skewHermitian_eq | exact GlobalTheory.finrank_skewHermitian_eq | (intros; apply GlobalTheory.finrank_skewHermitian_eq <;> assumption)

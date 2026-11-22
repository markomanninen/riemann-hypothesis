module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentMatchingIndependentOfCuspBasis
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
theorem _root_.GlobalTheory.T.exponentMatching_independent_of_cuspBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ N : ℕ) (X : Data E r) (cu₀ cu : FJ.CuspFD X ρ) (P : Matrix (Fin ρ) (Fin ρ) E), IsUnit P.det → (∀ a, cu₀.e a = ∑ b, P a b • cu.e b) → (∀ χ, FJ.IsHermE χ → ((∀ β ∈ FJ.zGam X cu, ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu), (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E))) → ∀ χ, FJ.IsHermE χ → ((∀ β ∈ FJ.zGam X cu₀, ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu₀), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu₀), (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E)) := by
  first | exact @GlobalTheory.CuspBasis.expoMatch_of_basis_change | exact GlobalTheory.CuspBasis.expoMatch_of_basis_change | (intros; apply GlobalTheory.CuspBasis.expoMatch_of_basis_change <;> assumption)

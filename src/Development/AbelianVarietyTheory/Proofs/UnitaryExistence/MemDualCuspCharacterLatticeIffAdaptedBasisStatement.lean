module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemDualCuspCharacterLatticeIffAdaptedBasis
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
theorem _root_.GlobalTheory.T.mem_dual_cuspCharacterLattice_iff_adapted_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) → ∀ u : Fin ρ → E, u ∈ FJ.dualOE (FJ.XcFD 1 cu) ↔ ∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → u a * y ∈ Set.range (algebraMap (𝓞 E) E) := by
  first | exact @GlobalTheory.mem_dualOE_xcFD_one_iff_of_adapted | exact GlobalTheory.mem_dualOE_xcFD_one_iff_of_adapted | (intros; apply GlobalTheory.mem_dualOE_xcFD_one_iff_of_adapted <;> assumption)

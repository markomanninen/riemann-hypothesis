module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartLieMultShift
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieMultIffExistsFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionTangentExactStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionModuleStructureStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceBasisExistsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenDecompositionExactSequenceStatement

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_part_lie_mult_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S) (P : AbPart t z), ∃ r : ℕ, ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k) (n : ℕ), LieMult P.tK.act (spMap g) τ n → r ≤ n ∧ LieMult P.tB.act (spMap g) τ (n - r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AbMult.lieMult_abPart | exact GlobalTheory.CompanionTheory.Ar.AbMult.lieMult_abPart | (intros; apply GlobalTheory.CompanionTheory.Ar.AbMult.lieMult_abPart <;> assumption)

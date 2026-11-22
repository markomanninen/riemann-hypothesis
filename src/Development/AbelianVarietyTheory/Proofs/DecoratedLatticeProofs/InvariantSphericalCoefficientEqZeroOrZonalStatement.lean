module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantSphericalCoefficientEqZeroOrZonal
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_sphericalCoefficient_eq_zero_or_zonal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), IsSatVecU (ϖ : L) q ρ x α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∀ k ∈ KU σ n, ∀ g, ℓ (ρ (k * g) x) = ℓ (ρ g x)) → (ℓ x = 0 → ∀ g, ℓ (ρ g x) = 0) ∧ (ℓ x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal (ϖ : L) q α fun g => ℓ (ρ g x) / ℓ x) := by
  first | exact @GlobalTheory.ZonalCoeff.coeff_zero_or_zonal | exact GlobalTheory.ZonalCoeff.coeff_zero_or_zonal | (intros; apply GlobalTheory.ZonalCoeff.coeff_zero_or_zonal <;> assumption)

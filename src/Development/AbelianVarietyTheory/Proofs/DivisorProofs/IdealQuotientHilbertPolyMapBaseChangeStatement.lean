module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyMapBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero

@[expose] public section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealQuotientHilbertPoly_map_baseChange : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (N : ℕ) (P : Ideal (MvPolynomial (Fin N) K)), (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → (∀ g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L), ∀ n : ℕ, homogeneousComponent n g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) ∧ GlobalTheory.idealHilbertPoly (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) = GlobalTheory.idealHilbertPoly P := by
  first | exact @GlobalTheory.HilbBaseChange.idealHilbertPoly_map | exact GlobalTheory.HilbBaseChange.idealHilbertPoly_map | (intros; apply GlobalTheory.HilbBaseChange.idealHilbertPoly_map <;> assumption)

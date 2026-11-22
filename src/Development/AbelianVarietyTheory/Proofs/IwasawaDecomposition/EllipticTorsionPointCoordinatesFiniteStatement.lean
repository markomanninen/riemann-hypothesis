module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllipticTorsionPointCoordinatesFinite
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ellipticTorsionPointCoordinates_finite : ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic] (n : ℕ), n ≠ 0 → (torsionCoords W n).Finite := by
  first | exact @GlobalTheory.finite_torsionCoords | exact GlobalTheory.finite_torsionCoords | (intros; apply GlobalTheory.finite_torsionCoords <;> assumption)

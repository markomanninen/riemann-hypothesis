module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mapDomain_fst_eq_of_coeff_matrixFamilyBilateralSubstitution_ne_zero : ∀ {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (k k' : ι × Fin N × Fin n →₀ ℕ), AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1)) k' ≠ 0 → Finsupp.mapDomain Prod.fst k' = Finsupp.mapDomain Prod.fst k := by
  first | exact @GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero | exact GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero | (intros; apply GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero <;> assumption)

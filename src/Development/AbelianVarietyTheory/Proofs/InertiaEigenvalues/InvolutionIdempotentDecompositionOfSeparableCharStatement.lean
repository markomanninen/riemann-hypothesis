module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutionIdempotentDecompositionOfSeparableChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero

@[expose] public section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.involutionIdempotentDecomposition_of_separable_charpoly : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∃ (ι : Type) (_ : Fintype ι) (e : ι → B.A) (S : Finset ι), IsPre B e S := by
  first | exact @GlobalTheory.UnitLemma.Desc.isPre_of_separable | exact GlobalTheory.UnitLemma.Desc.isPre_of_separable | (intros; apply GlobalTheory.UnitLemma.Desc.isPre_of_separable <;> assumption)

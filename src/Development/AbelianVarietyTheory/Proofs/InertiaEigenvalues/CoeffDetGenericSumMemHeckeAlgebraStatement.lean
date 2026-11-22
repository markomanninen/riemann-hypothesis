module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetGenericSumMemHeckeAlgebra
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_det_generic_sum_mem_heckeAlgebra : ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep → ∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, InRing T rep (a k)) → ∀ d : Fin m →₀ ℕ, (fun x => AddMonoidAlgebra.coeff (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d) ∈ T := by
  first | exact @GlobalTheory.SpanRing.coeff_det_generic_sum_mem_of_inRing | exact GlobalTheory.SpanRing.coeff_det_generic_sum_mem_of_inRing | (intros; apply GlobalTheory.SpanRing.coeff_det_generic_sum_mem_of_inRing <;> assumption)

module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedByCyclotomicKernelEtalePhiSolutionMemWach
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedByCyclotomicKernel_etalePhi_solution_mem_wach :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ)
      (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R),
      IoW I → ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin p) R.EE) (A' : Matrix (Fin q) (Fin q) R.EE)
      (Y : Matrix (Fin p) (Fin q) R.EE) (U : Matrix (Fin p) (Fin q) (RW LL)),
      IsUnit A → IsUnit A' → (∀ i j, FixH AI K (U i j)) →
      HMul.hMul (α := Matrix (Fin p) (Fin p) (RW LL)) (β := Matrix (Fin p) (Fin q) (RW LL))
        (A.map I.ioE) (U.map (φRW LL)) =
        HMul.hMul (α := Matrix (Fin p) (Fin q) (RW LL)) (β := Matrix (Fin q) (Fin q) (RW LL))
          U (A'.map I.ioE) + Y.map I.ioE → ∀ i j, U i j ∈ Set.range I.ioE := by
  intro l _ P AI K s LL hG Γ R I hW p q A A' Y U _ hA' hU h i j
  obtain ⟨C, hC⟩ := hA'.exists_right_inv
  let σ := (finProdFinEquiv : Fin p × Fin q ≃ Fin (p * q)).symm
  obtain ⟨e, he⟩ := GlobalTheory.HWL.Rational.vec hG I hW (p * q)
    (fun a b => A (σ a).1 (σ b).1 * C (σ b).2 (σ a).2)
    (fun a => U (σ a).1 (σ a).2) (fun a => hU _ _) (fun a => ⟨_,
      GlobalTheory.HWL.Rational.matrix_eq (I.ioE : R.EE →+* RW LL) (φRW LL : RW LL →+* RW LL)
        A A' C Y U hC h σ a⟩) (σ.symm (i, j))
  rw [σ.apply_symm_apply] at he
  exact ⟨e, he.symm⟩

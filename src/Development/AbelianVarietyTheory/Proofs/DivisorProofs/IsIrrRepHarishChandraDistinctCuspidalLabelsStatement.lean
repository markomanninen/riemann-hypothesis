module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrrRepHarishChandraDistinctCuspidalLabels
public import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity

@[expose] public section

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIrrRep_harishChandra_distinct_cuspidal_labels : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b → (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → ∀ (C : LabelConv K) (O : LabelMap K C), Function.Injective (fun c => labO O (lam c)) → IsIrrRep (hcRep K b lam) := by
  first | exact @GlobalTheory.HcIrr.isIrrRep_hcRep | exact GlobalTheory.HcIrr.isIrrRep_hcRep | (intros; apply GlobalTheory.HcIrr.isIrrRep_hcRep <;> assumption)

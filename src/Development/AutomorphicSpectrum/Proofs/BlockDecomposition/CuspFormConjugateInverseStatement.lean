module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormConjugateInverse
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_conjugate_inverse : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}, ∀ (φ : Sm E a) (hψ : (fun g => star (φ.1 (invA E a g))) ∈ Sm E a), IsCuspForm φ → IsCuspForm (⟨fun g => star (φ.1 (invA E a g)), hψ⟩ : Sm E a) := by
  first | exact @GlobalTheory.CompanionTheory.DualCusp.isCuspForm_conj_invA | exact GlobalTheory.CompanionTheory.DualCusp.isCuspForm_conj_invA | (intros; apply GlobalTheory.CompanionTheory.DualCusp.isCuspForm_conj_invA <;> assumption)

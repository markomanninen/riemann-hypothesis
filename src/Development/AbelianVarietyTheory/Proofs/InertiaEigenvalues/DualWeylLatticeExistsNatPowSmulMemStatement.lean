module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualWeylLatticeExistsNatPowSmulMem
public import Formalism.LocalToGlobal.Columns.CoefModAt
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPNabStdOfIsBasisAt

@[expose] public section

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylLattice_exists_natPow_smul_mem : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight n) (M M' : Submodule (𝓞 E) (Fin n → E)) (N : ℕ), N ≠ 0 → Submodule.IsFullLattice E M → Submodule.IsFullLattice E M' → (∀ x ∈ M, (N : 𝓞 E) • x ∈ M') → (∀ x ∈ M', (N : 𝓞 E) • x ∈ M) → ∃ a : ℕ, ∀ F ∈ Formalism.L2.DIV.nabAtr emb lam M, ((N : K) ^ a) • F ∈ Formalism.L2.DIV.nabAtr emb lam M' := by
  first
  | exact @GlobalTheory.NabScale.nabAtr_smul_pow_mem
  | intro E K _ _ _ _ ι _ n emb lam M M' N hN hM hM' h1 h2
    exact GlobalTheory.NabScale.nabAtr_smul_pow_mem E K ι n emb lam M M' N hN
      hM.toIsLattice hM'.toIsLattice h1 h2

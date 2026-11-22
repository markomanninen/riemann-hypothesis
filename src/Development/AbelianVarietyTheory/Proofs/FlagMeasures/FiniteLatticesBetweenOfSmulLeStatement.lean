module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteLatticesBetweenOfSmulLe
public import Formalism.HermitianLattices.FinalNeighbourConstruct
public import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound

@[expose] public section

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_lattices_between_of_smul_le' : ∀ {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), M.FG → ∀ N : ℕ, 0 < N → {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ ∀ x ∈ Λ, (N : K) • x ∈ M}.Finite := by
  first | exact @GlobalTheory.finite_lattices_between_of_smul_le | exact GlobalTheory.finite_lattices_between_of_smul_le | (intros; apply GlobalTheory.finite_lattices_between_of_smul_le <;> assumption)

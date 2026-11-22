module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupBasisNhds
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_subgroup_basis_nhds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (U : Set (GL (Fin N) k)), IsOpen U → (1 : GL (Fin N) k) ∈ U → ∃ m : ℕ, 1 ≤ m ∧ (Zls.Km k N m : Set (GL (Fin N) k)) ⊆ U := by
  first | exact @GlobalTheory.CompanionTheory.CongruenceBasis.exists_Km_subset | exact GlobalTheory.CompanionTheory.CongruenceBasis.exists_Km_subset | (intros; apply GlobalTheory.CompanionTheory.CongruenceBasis.exists_Km_subset <;> assumption)

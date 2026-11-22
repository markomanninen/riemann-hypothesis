module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieMemCompactFiniteVectorsOfMem
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_mem_compactFiniteVectors_of_mem : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (X : Lie E N) (φ : Sm E N), φ ∈ finVec (cptRep E N) → lie E N X φ ∈ finVec (cptRep E N) := by
  first | exact @GlobalTheory.LieFin.lie_mem_finVec | exact GlobalTheory.LieFin.lie_mem_finVec | (intros; apply GlobalTheory.LieFin.lie_mem_finVec <;> assumption)

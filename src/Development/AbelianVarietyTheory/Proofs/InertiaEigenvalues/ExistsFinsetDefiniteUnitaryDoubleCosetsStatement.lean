module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDefiniteUnitaryDoubleCosets
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatAtConstOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivLocProdTriv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteClassSetHermitianUnitaryOpenLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_definiteUnitary_doubleCosets : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ L : Subgroup (finU (E := E) (n := n)), IsOpen (L : Set (finU (E := E) (n := n))) → ∃ S : Finset (UA E n), ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ k ∈ L, ∃ y ∈ infU E n, g = γ * s * (k : UA E n) * y := by
  first | exact @GlobalTheory.UnitaryBC.ClassTransport.exists_finset_double_cosets | exact GlobalTheory.UnitaryBC.ClassTransport.exists_finset_double_cosets | (intros; apply GlobalTheory.UnitaryBC.ClassTransport.exists_finset_double_cosets <;> assumption)

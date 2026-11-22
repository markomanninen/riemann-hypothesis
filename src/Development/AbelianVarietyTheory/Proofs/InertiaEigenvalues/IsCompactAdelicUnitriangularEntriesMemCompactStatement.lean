module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCompactAdelicUnitriangularEntriesMemCompact
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
public import GroundTheory.GlobalFields.Adele.Discrete
public import GroundTheory.GlobalFields.Adele.IntegersLattice

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_adelicUnitriangular_entries_mem_compact : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (C : Set (Ad E)), IsCompact C →
    IsCompact {g : GA E n | g ∈ GlobalTheory.CellDec.NA E n ∧ ∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} := by
  first | exact @GlobalTheory.CellDec.isCompact_unip_entries_mem | exact GlobalTheory.CellDec.isCompact_unip_entries_mem | (intros; apply GlobalTheory.CellDec.isCompact_unip_entries_mem <;> assumption)

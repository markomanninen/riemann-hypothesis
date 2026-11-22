module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueRatUnitriangularMulEntriesMemFundame
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
public import GroundTheory.GlobalFields.Adele.Discrete
public import GroundTheory.GlobalFields.Adele.IntegersLattice

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_ratUnitriangular_mul_entries_mem_fundamentalSet : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (u : GA E n), u ∈ GlobalTheory.CellDec.NA E n →
    ∃! γ : GL (Fin n) E, γ ∈ GlobalTheory.SmGL.unipB E (Fin n) ∧ ∀ i j : Fin n, i < j →
      ((ratGL E n γ * u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ GroundTheory.Global.fundamentalSet E := by
  first | exact @GlobalTheory.CellDec.existsUnique_ratUnip_mul_mem_fundamentalSet | exact GlobalTheory.CellDec.existsUnique_ratUnip_mul_mem_fundamentalSet | (intros; apply GlobalTheory.CellDec.existsUnique_ratUnip_mul_mem_fundamentalSet <;> assumption)

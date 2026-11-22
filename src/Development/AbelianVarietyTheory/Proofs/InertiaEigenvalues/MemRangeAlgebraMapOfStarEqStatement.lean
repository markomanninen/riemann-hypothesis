module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeAlgebraMapOfStarEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch

@[expose] public section

open GlobalTheory.UnitLemma Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_algebraMap_of_star_eq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (y : E), star y = y → ∃ x : F, algebraMap F E x = y := by
  first | exact @GlobalTheory.JR.Unram.mem_range_of_star_eq | exact GlobalTheory.JR.Unram.mem_range_of_star_eq | (intros; apply GlobalTheory.JR.Unram.mem_range_of_star_eq <;> assumption)

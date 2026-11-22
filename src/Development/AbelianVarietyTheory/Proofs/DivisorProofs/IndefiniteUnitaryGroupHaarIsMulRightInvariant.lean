module

public import Mathlib
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian

@[expose] public section

open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory

theorem haar_UJ_isMulRightInvariant : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  intro n ε μ _
  have hR : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  rw [Measure.isMulLeftInvariant_eq_smul μ (Formalism.REAL.muG ε)]
  exact ⟨fun g => by
    rw [Measure.map_smul, hR.map_mul_right_eq_self]
    exact (measurable_mul_const g).aemeasurable⟩

end GlobalTheory

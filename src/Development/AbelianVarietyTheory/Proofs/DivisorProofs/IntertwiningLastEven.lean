module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemWeylCellUnitaryGroupLongSimpleReflectionIffStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalVectorValueUnitaryRankOneGindikinKarpelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylCellStabilizerMeasure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqRankOneFactorSL2OfGeometricOnShellsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalWeylCellTranslate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryBorelEqDiagonalMulUnipotentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylCellStabilizerMeasureTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiDeltaUConjLongSimpleReflectionUnitaryStatement

@[expose] public section

noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

namespace GlobalTheory.WeylCell.RankOneUnitary

theorem chiDeltaU_congr {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n m : ℕ}
    (q : ℕ) (α : Fin m → ℂ) (b c : GU σ n)
    (h : ∀ i, ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = ((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) :
    chiDeltaU q α b = chiDeltaU q α c := by
  unfold chiDeltaU
  simp only [h]

end GlobalTheory.WeylCell.RankOneUnitary

namespace GlobalTheory.WeylCell.RankOneUnitary

theorem ordL_of_v_eq {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (x : L) (z : ℤ)
    (hx : Valued.v x = ((Multiplicative.ofAdd z : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) : ordL x = -z := by
  unfold ordL
  have h0 : Valued.v x ≠ 0 := by rw [hx]; exact WithZero.coe_ne_zero
  rw [dite_eq_right h0]
  have : WithZero.unzero h0 = Multiplicative.ofAdd z := by
    apply WithZero.coe_injective; rw [WithZero.coe_unzero, hx]
  rw [this]; rfl

end GlobalTheory.WeylCell.RankOneUnitary

end

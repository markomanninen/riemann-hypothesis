module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLatticeBasis
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexDet
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIsLattice
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexTrans
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIdealLatticeFG
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLineDegree
public import GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights

noncomputable section

theorem genIndex_eq_div_of_le {M : Type*} [AddCommGroup M] {A B C : AddSubgroup M} (hCA : C ≤ A)
    (hCB : C ≤ B) (hC : C.relIndex B ≠ 0) :
    genIndex A B = (C.relIndex A : ℝ) / (C.relIndex B : ℝ) := by
  have h1 : C.relIndex (A ⊓ B) * B.relIndex A = C.relIndex A := by
    rw [← AddSubgroup.inf_relIndex_left A B]
    exact AddSubgroup.relIndex_mul_relIndex _ _ _ (le_inf hCA hCB) inf_le_left
  have h2 : C.relIndex (A ⊓ B) * A.relIndex B = C.relIndex B := by
    rw [← AddSubgroup.inf_relIndex_right A B]
    exact AddSubgroup.relIndex_mul_relIndex _ _ _ (le_inf hCA hCB) inf_le_right
  have h3 : (C.relIndex (A ⊓ B) : ℝ) ≠ 0 := by
    intro h
    apply hC
    rw [← h2, Nat.cast_eq_zero.mp h, zero_mul]
  unfold genIndex
  rw [← h1, ← h2]
  push_cast
  rw [mul_div_mul_left _ _ h3]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

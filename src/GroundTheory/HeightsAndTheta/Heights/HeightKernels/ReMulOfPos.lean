module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
public import GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLatticeBasis
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexDet
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIsLattice
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexTrans
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIdealLatticeFG
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLineDegree

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors ComplexOrder

noncomputable section

theorem gramAt_single {K : Type*} [Field K] {k : ℕ} (h : Matrix (Fin k) (Fin k) ℂ) (σ : K →+* ℂ) :
    gramAt h σ (fun j : Fin k => (Pi.single j 1 : Fin k → K)) = h := by
  have he : ∀ j : Fin k, embVec σ (Pi.single j 1 : Fin k → K) = Pi.single j 1 := fun j => by
    funext i
    by_cases hij : i = j
    · subst hij; simp [embVec]
    · simp [embVec, hij]
  ext a b
  simp [gramAt, he, mulVec_single, single_dotProduct]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagR
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Assembly

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

theorem mCoordIdeal_eq_ker_multiConeMap {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Φ : Type} [Field Φ] (c : (Σ k, ι k) → Φ) : mCoordIdeal c = RingHom.ker (T.multiConeMap c) := by
  have h : (mConeMap c : MRing ι →+* MvPolynomial K Φ) = T.multiConeMap c :=
    MvPolynomial.ringHom_ext (fun r => by simp [T.multiConeMap, mConeMap])
      (fun p => by simp [T.multiConeMap, mConeMap])
  rw [mCoordIdeal, ← h]
  rfl

end

end GroundTheory.Heights₂.Heights.Inter

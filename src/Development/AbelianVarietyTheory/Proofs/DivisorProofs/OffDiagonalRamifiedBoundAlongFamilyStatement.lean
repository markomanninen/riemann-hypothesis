module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagonalRamifiedBoundAlongFamily
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.offDiagonalRamified_bound_along_family' : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.DiscriminantOffsetBound (Fm.D x i) (Fm.L x i) C := by
  first | exact @GlobalTheory.RamifiedOffD.offDiagonalRamified_bound_along_family | exact GlobalTheory.RamifiedOffD.offDiagonalRamified_bound_along_family | (intros; apply GlobalTheory.RamifiedOffD.offDiagonalRamified_bound_along_family <;> assumption)

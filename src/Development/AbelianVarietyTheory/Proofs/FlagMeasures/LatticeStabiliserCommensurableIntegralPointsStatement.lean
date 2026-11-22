module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabiliserCommensurableIntegralPoints
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerStabilizersCommensurableVolume
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeMassEqFinprodLocalStatement

@[expose] public section

open NumberField GlobalTheory.HL
open scoped Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeStabiliser_commensurable_integralPoints : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → (G.stabL Λ).relIndex G.K0 ≠ 0 ∧ G.K0.relIndex (G.stabL Λ) ≠ 0 := by
  intro F E _ _ _ _ _ sig A r k G hk Λ hΛ
  exact GlobalTheory.HL.CommInt.stabL_relIndex_K0_ne_zero_of_four_mul_add_seven_le A r k G hk Λ
    (by first | exact hΛ | exact hΛ.toIsLattice)

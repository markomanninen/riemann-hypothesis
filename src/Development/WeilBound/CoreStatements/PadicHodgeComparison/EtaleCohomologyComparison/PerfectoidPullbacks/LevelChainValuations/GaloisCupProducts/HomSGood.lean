module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomLevGood
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InclRedM
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DPullCEqZero

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (M : Model l K) {s s' : ℕ} (h : s ≤ s')
  (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
  (hQ' : ∀ T, QB L M s' T → QA L M s' (((nmB M hL).mor 0).obj T))
  (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)
  (rH' : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s') none ((l : L.A) ^ n) j)

theorem homS_good_of_inclHM (hr : ∀ n j x, inclHM M h n j (rH' n j x) = rH n j x) :
    (homS hL M h hQ hQ' rH rH').Good := by
  constructor
  · rfl
  · intro c
    rfl
  · intro a
    rfl
  · intro k
    rfl
  · intro n j x
    rfl
  · intro n j x
    exact hr n j x
  · intro n j z
    exact GlobalTheory.CompanionTheory.RedPull.incl_redM
      (ts_le L.γ M.p l h {⊤}) none ((l : L.A) ^ n) j z
  · intro j z
    exact bMap_incl hL M h hQ hQ' j z
  · intro j v
    exact GlobalTheory.CompanionTheory.MuThick.muB_incl
      L.γB M.q 1 s s' {⊤} (ts_le L.γB M.q 1 h {⊤}) j v

end

end CrystallineSemistableComparison.Pb.Kap

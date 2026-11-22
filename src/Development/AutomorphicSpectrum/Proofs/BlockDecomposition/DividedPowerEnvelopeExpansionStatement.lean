module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeExpansion
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsDividedPowersAug
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.FilIsSubDPIdeal
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.RingTrunc
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerPolynomialFiltrationStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleLiftingOfNilIdealStatement

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divided_power_envelope_expansion : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (z : (pq B).P), ∃ b : ℕ →₀ B, z = b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1) := by
  first | exact @GlobalTheory.CompanionTheory.PDSpanning.exists_sum_dpow | exact GlobalTheory.CompanionTheory.PDSpanning.exists_sum_dpow | (intros; apply GlobalTheory.CompanionTheory.PDSpanning.exists_sum_dpow <;> assumption)

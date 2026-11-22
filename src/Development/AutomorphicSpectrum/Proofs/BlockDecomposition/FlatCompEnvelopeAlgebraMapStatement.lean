module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatCompEnvelopeAlgebraMap
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
theorem _root_.GlobalTheory.T.flat_comp_envelope_algebraMap : ∀ {A B : Type} [CommRing A] [CommRing B] (i : A →+* B), i.Flat → ((algebraMap B (pq B).P).comp i).Flat := by
  first | exact @GlobalTheory.CompanionTheory.SitePD.pdPoly_flat_comp | exact GlobalTheory.CompanionTheory.SitePD.pdPoly_flat_comp | (intros; apply GlobalTheory.CompanionTheory.SitePD.pdPoly_flat_comp <;> assumption)

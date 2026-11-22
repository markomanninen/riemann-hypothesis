module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CMLatticeDividedPowerJetIntegralityOfHyp
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLatticeDividedPowerJetIntegrality_of_ellipticCM : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatJet.JetInt := by
  first | exact @GlobalTheory.JetIntElliptic.jetInt | exact GlobalTheory.JetIntElliptic.jetInt | (intros; apply GlobalTheory.JetIntElliptic.jetInt <;> assumption)

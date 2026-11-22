module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPeriodZetaOfJetIntegralityAlgebra
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricPeriodZetaStatements_of_jetIntegrality_algebraicity : GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.LatJet.JetInt → GlobalTheory.LatVal.LatAlg → GlobalTheory.LatVal.LatConj → GlobalTheory.Mem.LiteralAutomorphy.JoinOut := by
  first | exact @GlobalTheory.JoinFun.joinOut_of_jetInt | exact GlobalTheory.JoinFun.joinOut_of_jetInt | (intros; apply GlobalTheory.JoinFun.joinOut_of_jetInt <;> assumption)

module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIsAlgebraicOfEllipticCMTheorems
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeValueIsAlgebraic_of_ellipticCM_theorems : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatVal.LatAlg := by
  first | exact @GlobalTheory.RoadELatAlg.latAlg_of_siegelKlingen | exact GlobalTheory.RoadELatAlg.latAlg_of_siegelKlingen | (intros; apply GlobalTheory.RoadELatAlg.latAlg_of_siegelKlingen <;> assumption)

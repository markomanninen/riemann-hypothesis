module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinExpansionOfLipschitzHeckeZeta
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation

@[expose] public section

open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisensteinExpansion_of_lipschitz_hecke_zeta : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo → GlobalTheory.Published.PartialZetaFunctionalEquation → EisExp := by
  first | exact @GlobalTheory.HilbertEis.eisExp | exact GlobalTheory.HilbertEis.eisExp | (intros; apply GlobalTheory.HilbertEis.eisExp <;> assumption)

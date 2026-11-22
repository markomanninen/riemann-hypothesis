module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelLatticeMapKilledByPrimePow
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RepresentationBounds

@[expose] public section

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cokernel_latticeMap_killed_by_prime_pow : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Stmt := by
  first | exact @GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main | exact GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main | (intros; apply GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main <;> assumption)

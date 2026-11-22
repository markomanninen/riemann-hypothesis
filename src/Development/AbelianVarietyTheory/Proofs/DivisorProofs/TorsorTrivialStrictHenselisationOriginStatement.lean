module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialStrictHenselisationOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial

@[expose] public section

open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsor_trivial_strict_henselisation_origin : GlobalTheory.LocAcyc.KeyOrigin := by
  first | (exact @GlobalTheory.KeyOriginCut.keyOrigin) | (exact GlobalTheory.KeyOriginCut.keyOrigin) | (intros; apply GlobalTheory.KeyOriginCut.keyOrigin  <;> assumption)

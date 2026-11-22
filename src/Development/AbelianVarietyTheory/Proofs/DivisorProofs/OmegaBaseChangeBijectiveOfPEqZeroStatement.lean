module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeBijectiveOfPEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero

@[expose] public section

open GlobalTheory.PDiv

theorem GlobalTheory.T.omega_baseChange_bijective_of_p_eq_zero {p : ℕ} {R : Type}
    [CommRing R] (G : GlobalTheory.PDivGroup p R) (R' : Type) [CommRing R'] [Algebra R R']
    (hp : (p : R) = 0) : Function.Bijective (liftSemi (G.toBase R').omega) :=
  G.omega_baseChange_bijective R' hp

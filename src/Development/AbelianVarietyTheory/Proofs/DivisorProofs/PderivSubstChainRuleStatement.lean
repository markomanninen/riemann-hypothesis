module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PderivSubstChainRule
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pderiv_subst_chain_rule :
    ∀ {R σ τ : Type} [CommRing R] [Fintype σ] [Fintype τ] (a : σ → MvPowerSeries τ R),
      (∀ s, constantCoeff (a s) = 0) → ∀ (f : MvPowerSeries σ R) (k : τ),
        pderiv (R := R) k (subst a f) = ∑ j, subst a (pderiv (R := R) j f) * pderiv (R := R) k (a j) := by
  exact @GlobalTheory.PSChain.pderiv_subst_chain

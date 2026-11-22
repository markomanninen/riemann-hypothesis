module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIntegralClosureAlgClosu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monicPolynomialsHaveRoots_integralClosure_algClosure : ∀ (D : Type) [CommRing D] [IsDomain D], AIC (integralClosure D (AlgebraicClosure (FractionRing D))) := by
  first | (exact @GlobalTheory.aic_integralClosure_algebraicClosure) | (exact GlobalTheory.aic_integralClosure_algebraicClosure) | (intros; apply GlobalTheory.aic_integralClosure_algebraicClosure  <;> assumption)

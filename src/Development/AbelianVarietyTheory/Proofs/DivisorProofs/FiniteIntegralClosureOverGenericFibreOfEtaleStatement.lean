module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIntegralClosureOverGenericFibreOfEtale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIffEtaleAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorExistsPointFiniteSeparable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeIsDomainIsIntegrallyClos

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_integralClosureOverGenericFibre_of_etale : ∀ (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [Algebra A R] [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    Module.Finite R (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  first | (exact @GlobalTheory.KeyOriginNoeth.finite_closure) | (exact GlobalTheory.KeyOriginNoeth.finite_closure) | (intros; apply GlobalTheory.KeyOriginNoeth.finite_closure <;> assumption)

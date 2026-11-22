module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CartanExchangeUnimodularInertPrime
public import Formalism.LocalToGlobal.Columns.HeckeInertComm
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PatchAtSelf

@[expose] public section

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartan_exchange_unimodular_inert_prime : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (n : ℕ), CartanInert E n := by
  first | exact @GlobalTheory.CartanInertPf.cartanInert | exact GlobalTheory.CartanInertPf.cartanInert | (intros; apply GlobalTheory.CartanInertPf.cartanInert <;> assumption)

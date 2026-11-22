module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomNmulOfIsLaw

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory.NMulHom

theorem isHom_nmul : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    IsLaw μ → ∀ n, IsHom μ μ (nmul μ n) :=
  GlobalTheory.NMulEndo.isHom_nmul

end GlobalTheory.NMulHom

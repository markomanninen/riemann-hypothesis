module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeStabilizerConjFiniteAdeleGLIntegral
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.BorelGL
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_stabilizer_conj_finiteAdeleGL_integral : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)), ∃ Λ : Submodule (𝓞 F) (Fin n → F), Submodule.IsFullLattice F Λ ∧ ∀ γ : GL (Fin n) F, (∀ y, (γ : Matrix (Fin n) (Fin n) F) *ᵥ y ∈ Λ ↔ y ∈ Λ) → s⁻¹ * PIW.ClassFinD.glIncl F n γ * s ∈ PIW.ClassFinD.KGL F n := by
  intro F _ _ n s
  let Λ := GlobalTheory.StabLat.lat F s
  have hΛ : Submodule.IsFullLattice F Λ :=
    { toIsLattice := Submodule.IsLattice.of_fg F (GlobalTheory.StabLat.lat_fg s)
      span_eq_top := GlobalTheory.StabLat.lat_span s }
  refine ⟨Λ, hΛ, fun γ hγ => ⟨GlobalTheory.StabLat.matInt_conj s γ fun y hy => (hγ y).2 hy, ?_⟩⟩
  have hinv : (s⁻¹ * PIW.ClassFinD.glIncl F n γ * s)⁻¹ =
      s⁻¹ * PIW.ClassFinD.glIncl F n γ⁻¹ * s := by
    rw [map_inv]; group
  rw [hinv]
  refine GlobalTheory.StabLat.matInt_conj s γ⁻¹ fun y hy => ?_
  rw [← hγ, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  exact hy

module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysLatOfTrivial

@[expose] public section

noncomputable section

namespace GlobalTheory.HWL.Back

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct
open scoped Classical

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {W : LocWach PD LL O v n} {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA}
    {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}


theorem tmul_cancel (hO : Function.Injective (algebraMap O LL)) (W : LocWach PD LL O v n)
    (e₀ : ↥W.one.L.T) (h₀ : Submodule.span O {e₀} = ⊤) {r r' : RW}
    (h : (r ⊗ₜ[O] e₀ : TW RW W.one) = r' ⊗ₜ[O] e₀) : r = r' := by
  obtain ⟨e, he, hT⟩ := W.one_line
  have hne : (e₀ : W.one.V) ≠ 0 := by
    intro h0
    have heT : e ∈ W.one.L.T := hT ▸ Submodule.mem_span_singleton_self e
    have : (⟨e, heT⟩ : ↥W.one.L.T) ∈ Submodule.span O {e₀} := h₀ ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp this
    apply he
    have := congrArg Subtype.val ha
    simp only [Submodule.coe_smul, h0, smul_zero] at this
    exact this.symm
  have hbij : Function.Bijective (LinearMap.toSpanSingleton O ↥W.one.L.T e₀) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro a ha
      have := congrArg Subtype.val ha
      simp only [LinearMap.toSpanSingleton_apply, Submodule.coe_smul, Submodule.coe_zero] at this
      rw [← algebraMap_smul LL a, smul_eq_zero] at this
      exact hO (by rw [this.resolve_right hne, map_zero])
    · rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton, h₀]
  let ψ := (LinearEquiv.ofBijective _ hbij).symm
  have hψ : ψ e₀ = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    simp
  have := congrArg (fun x => TensorProduct.rid O RW (LinearMap.lTensor RW ψ.toLinearMap x)) h
  simpa [hψ] using this

theorem ioE_φ (hO : Function.Injective (algebraMap O LL))
    (E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA) (a : W.EE) : E.ioE (W.φE a) = φR (E.ioE a) := by
  obtain ⟨e, e₀, h₀, he, -⟩ := E.one_e
  have h1 := E.jD_φ W.one (a • e)
  rw [W.φD_smul, E.jD_smul, E.jD_smul, E.jD_φ, he] at h1
  simp only [TWmap, smul_tmul', smul_eq_mul, mul_one, map_tmul, AlgHom.toLinearMap_apply, map_one,
    LinearMap.id_apply] at h1
  exact tmul_cancel hO W e₀ h₀ h1

theorem ioE_γ (hO : Function.Injective (algebraMap O LL))
    (E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA) (g : G) (a : W.EE) :
    E.ioE (W.γE (W.resΓ g) a) = gR g (E.ioE a) := by
  obtain ⟨e, e₀, h₀, he, -⟩ := E.one_e
  have h1 := E.jD_act W.one g (a • e)
  have h2 : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g _)
  rw [W.γD_smul, E.jD_smul, E.jD_smul, E.jD_act, he] at h1
  simp only [TWact, smul_tmul', smul_eq_mul, mul_one, map_tmul, AlgHom.toLinearMap_apply, map_one,
    h2] at h1
  exact tmul_cancel hO W e₀ h₀ h1





end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime]


end Concrete

end GlobalTheory.HWL.Back

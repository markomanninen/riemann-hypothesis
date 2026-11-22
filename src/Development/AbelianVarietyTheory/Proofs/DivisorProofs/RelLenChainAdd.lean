module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory

theorem relLen_chain_add : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type)
    [AddCommGroup M] [Module (Int0 v) M] (X'' X' X : Submodule (Int0 v) M) (r₁ r₂ : ℝ),
    RelLen v X'' X' r₂ → RelLen v X' X r₁ → RelLen v X'' X (r₁ + r₂) := by
  intro C _ v M _ _ X'' X' X r₁ r₂ h₂ h₁
  obtain ⟨n, b, b', A, hA, hrA⟩ := h₁
  obtain ⟨m, c, c', B, hB, hrB⟩ := h₂
  have hnm : n = m := by simpa using Fintype.card_congr (b'.indexEquiv c)
  subst m
  have le_of_basis : ∀ {Y Z : Submodule (Int0 v) M}
      (d : Basis (Fin n) (Int0 v) Y) (e : Basis (Fin n) (Int0 v) Z)
      (D : Matrix (Fin n) (Fin n) (Int0 v)),
      (∀ k, (e k : M) = ∑ i, D i k • (d i : M)) → Z ≤ Y := by
    intro Y Z d e D h x hx
    have hx' : (x : M) = ∑ k, e.repr ⟨x, hx⟩ k • (e k : M) := by
      have hh := congrArg Z.subtype (e.sum_repr ⟨x, hx⟩)
      rw [map_sum] at hh
      exact hh.symm
    rw [hx']
    exact Y.sum_mem fun k _ => Y.smul_mem _ (by
      rw [h k]
      exact Y.sum_mem fun i _ => Y.smul_mem _ (d i).2)
  have hle₁ : X' ≤ X := le_of_basis b b' A hA
  have hle₂ : X'' ≤ X' := le_of_basis c c' B hB
  have key : ∀ {Y Z : Submodule (Int0 v) M} (h : Z ≤ Y)
      (d : Basis (Fin n) (Int0 v) Y) (e : Basis (Fin n) (Int0 v) Z)
      (D : Matrix (Fin n) (Fin n) (Int0 v)),
      (∀ k, (e k : M) = ∑ i, D i k • (d i : M)) →
      LinearMap.toMatrix e d (Submodule.inclusion h) = D := by
    intro Y Z h d e D hD
    ext i k
    have hh : Submodule.inclusion h (e k) = ∑ i, D i k • d i := by
      apply Subtype.ext
      simpa using hD k
    rw [LinearMap.toMatrix_apply, hh]
    simp [Finsupp.single_apply]
  have hmat₁ := key hle₁ b b' A hA
  have hmat₂ := key hle₂ c c' B hB
  let D := LinearMap.toMatrix c' b (Submodule.inclusion (hle₂.trans hle₁))
  have hD : D = A * (b'.toMatrix c) * B := by
    have hc : Submodule.inclusion (hle₂.trans hle₁) =
        (Submodule.inclusion hle₁).comp (Submodule.inclusion hle₂) := by
      ext x; rfl
    dsimp [D]
    rw [hc, LinearMap.toMatrix_comp c' b' b, hmat₁]
    rw [← basis_toMatrix_mul_linearMap_toMatrix c' b' c (Submodule.inclusion hle₂), hmat₂, Matrix.mul_assoc]
  refine ⟨n, b, c', D, ?_, ?_⟩
  · intro k
    have hh := b.sum_repr (Submodule.inclusion (hle₂.trans hle₁) (c' k))
    have hh' := congrArg X.subtype hh
    rw [map_sum] at hh'
    simpa [D, LinearMap.toMatrix_apply] using hh'.symm
  · have hu : IsUnit (b'.toMatrix c).det := by
      letI := b'.invertibleToMatrix c
      exact Matrix.isUnit_det_of_invertible _
    rw [hD, Matrix.det_mul, Matrix.det_mul, Subring.coe_mul, Subring.coe_mul,
      v.map_mul, v.map_mul, v_unit v hu, add_zero, hrA, hrB]
    simp

end GlobalTheory

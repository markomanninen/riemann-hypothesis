module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaModuleSaturationTheorem
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv

@[expose] public section

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phiGammaModule_saturation_theorem :
    ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l)
      {n : ℕ} [NeZero n]
      {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
      [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
      [FiniteDimensional k⸨X⸩ V]
      {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W]
      [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W]
      [FiniteDimensional k⸨X⸩ W]
      (D : ModPG R n V) (D' : ModPG R n W) (f : ZMod n → W →ₗ[k⸨X⸩] V),
      (∀ i, Function.Injective (f i)) →
      (∀ i x, f i (D'.φ i x) = D.φ i (f (i - 1) x)) →
      (∀ i x, f i (D'.γ i x) = D.γ i (f i x)) →
      ∀ (w w' : ZMod n → ℤ) (N : ZMod n → Submodule k⟦X⟧ V),
        (∀ i, IsLat (N i)) → CondAB D.φ w w' N → (∀ i, CondC (D.γ i) (N i)) →
        let N' := fun i => (N i).comap ((f i).restrictScalars k⟦X⟧);
        (∀ i, IsLat (N' i)) ∧ CondAB D'.φ w w' N' ∧ ∀ i, CondC (D'.γ i) (N' i) := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ D D' f hf hφ hγ w w' N hN hAB hC
  refine ⟨fun i => Sat.isLat_comap _ (hf i) (hN i), fun i => ?_, fun i x hx => ?_⟩
  · have h := Sat.comap_pull D D' i (f (i - 1)) (f i) (hf _) (hf _) (hφ i) (hN (i - 1)).1
    rw [← h, ← Sat.comap_sh, ← Sat.comap_sh]
    exact ⟨Submodule.comap_mono (hAB i).1, Submodule.comap_mono (hAB i).2⟩
  · rw [← Sat.comap_sh]
    change f i _ ∈ sh 1 (N i)
    rw [map_sub, hγ]
    exact hC i _ hx

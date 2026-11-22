module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPFlat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero

@[expose] public section

open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mulP_flat' : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R) (n : ℕ), RingHom.Flat ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  intro p R _ G n
  obtain ⟨hassoc, hcounit, hsurj⟩ := G.transl_free n
  obtain ⟨-, -, hff, -⟩ :=
    GlobalTheory.HopfQuot.finite_faithfullyFlat_ker (G.transl n) hassoc hcounit hsurj
  let B := AlgHom.equalizer (G.transl n)
    (Algebra.TensorProduct.includeLeft : G.A (n + 1) →ₐ[R] G.A (n + 1) ⊗[R] G.A 1)
  let f : G.A n →ₐ[R] B := AlgHom.codRestrict
    (G.mulP n : G.A n →ₐ[R] G.A (n + 1)) B (fun a => G.transl_mulP n a)
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => GlobalTheory.PDivGroup.Test.mulP_injective G n
      (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨a, ha⟩ := G.exists_mulP_eq_of_transl_eq n y.1 y.2
    exact ⟨a, Subtype.ext ha⟩
  have hB : RingHom.Flat (algebraMap B (G.A (n + 1))) := by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have hflat : RingHom.Flat (f : G.A n →+* B) := RingHom.Flat.of_bijective hf
  convert RingHom.Flat.comp hflat hB using 1
  exact RingHom.ext fun a => rfl

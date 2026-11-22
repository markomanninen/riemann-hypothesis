module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisRest

@[expose] public section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

namespace GlobalTheory.PlaneSkew

theorem exists_ne_zero_smul_mem_of_mem_span {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (L : Set (Fin n → E))) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.HermitianEigenvalueInequality.main
  | exact _root_.GlobalTheory.HermitianEigenvalueInequality.main
  | (apply _root_.GlobalTheory.HermitianEigenvalueInequality.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.HermitianEigenvalueInequality.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.HermitianEigenvalueInequality.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.HermitianEigenvalueInequality.main ..)

theorem isLattice_lowLat : ∀ (E : Type) [Field E] [NumberField E] (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (ι : Matrix (Fin n) (Fin n₁) E), L.IsLattice E → Function.Injective ι.mulVec → (lowLat ι L).IsLattice E := by
  intro E _ _ n n₁ L ι hL hι
  have hfg : L.FG := Submodule.IsLattice.fg (self := hL)
  refine ⟨?_, ?_⟩
  · let f : (Fin n₁ → E) →ₗ[𝓞 E] (Fin n → E) := (Matrix.mulVecLin ι).restrictScalars (𝓞 E)
    have hf : Function.Injective f := hι
    have hle : (lowLat ι L).map f ≤ L := Submodule.map_comap_le f L
    have hN : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian L hfg
    have hm : ((lowLat ι L).map f).FG := (isNoetherian_submodule.mp hN) _ hle
    exact Submodule.fg_of_fg_map_injective f hf hm
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end GlobalTheory.PlaneSkew

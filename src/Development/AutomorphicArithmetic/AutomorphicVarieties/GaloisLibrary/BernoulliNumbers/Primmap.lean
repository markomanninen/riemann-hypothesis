module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Condmap

@[expose] public section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_primmap :
    ∀ {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] {N : ℕ} [NeZero N] (f : R →+* S), Function.Injective f → ∀ (k : ℕ) (χ : DirichletCharacter R N), f (Bprim k χ) = Bprim k (χ.ringHomComp f) := by
  intro R S _ _ _ _ N _ f hf k χ
  obtain ⟨hcond, hval, -⟩ := b_condmap f hf χ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Bprim_eq, Bprim_eq, hcond, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_mul, hval a, RingHom.map_rat_algebraMap]

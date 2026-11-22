module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InjectiveOfIsCptGen

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory CptModel

namespace CoordInhab

variable {o K : Type} [CommRing o] [Field K] [Algebra o K]

theorem inv_mem_of_span_eq_top {κ : Type} (x : κ → o) (hx : Ideal.span (Set.range x) = ⊤) (c : κ)
    (S : Subring K) (h1 : ∀ a : o, algebraMap o K a ∈ S)
    (h2 : ∀ j, algebraMap o K (x j) / algebraMap o K (x c) ∈ S) : (algebraMap o K (x c))⁻¹ ∈ S := by
  have h1mem : (1 : o) ∈ Submodule.span o (Set.range x) := by
    have h : (1 : o) ∈ Ideal.span (Set.range x) := by
      rw [hx]
      exact Submodule.mem_top
    exact h
  have key : ∀ y ∈ Submodule.span o (Set.range x),
      algebraMap o K y / algebraMap o K (x c) ∈ S := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      exact h2 j
    | zero =>
      rw [map_zero, zero_div]
      exact S.zero_mem
    | add y z _ _ hy hz =>
      rw [map_add (f := _), add_div]
      exact S.add_mem hy hz
    | smul r y _ hy =>
      rw [smul_eq_mul, map_mul, mul_div_assoc]
      exact S.mul_mem (h1 r) hy
  have h := key 1 h1mem
  rwa [map_one, one_div] at h

theorem algebraMap_mem_regAt (p : Cpt (pt (algebraMap o K))) (a : o) :
    algebraMap o K a ∈ regAt (pt (algebraMap o K)) p :=
  RingHom.mem_range.2 ⟨tS p.1 a, genMap_toStalk _ p a⟩

variable [IsFractionRing o K]

theorem inChart_iff {κ : Type} (x : κ → o) (hx : Ideal.span (Set.range x) = ⊤) (c : κ)
    (p : Cpt (pt (algebraMap o K))) :
    InChart (pt (algebraMap o K)) (fun j => algebraMap o K (x j)) c p ↔ x c ∉ p.1.asIdeal := by
  have hinj := IsFractionRing.injective o K
  constructor
  · rintro ⟨hne, hrat⟩ hmem
    have hne' : algebraMap o K (x c) ≠ 0 := hne
    have hinv : (algebraMap o K (x c))⁻¹ ∈ regAt (pt (algebraMap o K)) p :=
      inv_mem_of_span_eq_top x hx c _ (algebraMap_mem_regAt p) hrat
    obtain ⟨b, s, hs, -, hbs⟩ := (mem_regAt_iff _ p _).1 hinv
    apply hs
    have hsb : algebraMap o K s = algebraMap o K (b * x c) := by
      rw [map_mul, ← hbs, mul_comm ((algebraMap o K (x c))⁻¹) (algebraMap o K s), mul_assoc,
        inv_mul_cancel₀ hne', mul_one]
    rw [hinj hsb]
    exact p.1.asIdeal.mul_mem_left b hmem
  · intro hnot
    have hne : algebraMap o K (x c) ≠ 0 := by
      intro h0
      apply hnot
      rw [(map_eq_zero_iff _ hinj).1 h0]
      exact p.1.asIdeal.zero_mem
    exact ⟨hne, fun c' => (mem_regAt_iff _ p _).2 ⟨x c', x c, hnot, hne, div_mul_cancel₀ _ hne⟩⟩

variable {R : Type} [CommRing R] [IsLocalRing R]

end CoordInhab

open CoordInhab

theorem ValAt.unique {X : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R] [IsLocalRing R]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r r' : R}
    (hξ : IsCptGen ξ) (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨hs, s, hsa, rfl⟩ := h
  obtain ⟨hs', s', hsa', rfl⟩ := h'
  exact congrArg (Scheme.stalkClosedPointTo z).hom (hξ.inj ⟨centre z, hs⟩ (hsa.trans hsa'.symm))

namespace CoordInhab

end CoordInhab

end GlobalTheory.CompanionTheory.Ar

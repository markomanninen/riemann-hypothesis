module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.Torus2GammaBijective

@[expose] public section

open TensorProduct Coalgebra AddMonoidAlgebra

namespace GlobalTheory

section Units

variable {A : Type*} [CommRing A] {X : Type*} [AddCommGroup X]

variable [IsDomain A]

variable [Module.Free ℤ X]


end Units

section Coordinates

variable {X : Type*} [Zero X] {N : Type*} [AddCommGroup N]

theorem coboundary_apply_zero_left (g : X →₀ N) (x : X) :
    (g.mapDomain (fun y => ((0 : X), y)) - g.mapDomain (fun y => (y, y)) +
      g.mapDomain (fun y => (y, (0 : X))) : X × X →₀ N) (0, x) = g x := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.sub_apply] at hf hg ⊢
    rw [← hf, ← hg]; abel
  | single y m =>
    simp only [Finsupp.mapDomain_single, Finsupp.add_apply, Finsupp.sub_apply,
      Finsupp.single_apply, Prod.mk.injEq]
    by_cases h : y = 0
    · subst h; simp
    · simp [h]

theorem finsupp_two_cocycle_eq_coboundary (f : X × X →₀ N)
    (hf : f.mapDomain (fun p => ((0 : X), p.1, p.2)) - f.mapDomain (fun p => (p.1, p.1, p.2)) +
      f.mapDomain (fun p => (p.1, p.2, p.2)) - f.mapDomain (fun p => (p.1, p.2, (0 : X))) = 0)
    (g : X →₀ N) (hg : ∀ x, g x = f (0, x)) :
    g.mapDomain (fun y => ((0 : X), y)) - g.mapDomain (fun y => (y, y)) +
      g.mapDomain (fun y => (y, (0 : X))) = f := by
  classical
  let s : (X × X →₀ N) →+ (X →₀ N) :=
    Finsupp.comapDomain.addMonoidHom (f := fun x => ((0 : X), x)) (Prod.mk_right_injective 0)
  have hs : ∀ f x, s f x = f (0, x) := fun _ _ => rfl
  have key : ∀ (f : X × X →₀ N) (q : X × X),
      (f.mapDomain (fun p => ((0 : X), p.1, p.2)) - f.mapDomain (fun p => (p.1, p.1, p.2)) +
        f.mapDomain (fun p => (p.1, p.2, p.2)) - f.mapDomain (fun p => (p.1, p.2, (0 : X))) :
          X × X × X →₀ N) (0, q) +
      ((s f).mapDomain (fun y => ((0 : X), y)) - (s f).mapDomain (fun y => (y, y)) +
        (s f).mapDomain (fun y => (y, (0 : X))) : X × X →₀ N) q = f q := by
    intro f q
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
      simp only [map_add (f := _), Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.sub_apply] at hf hg ⊢
      rw [← hf, ← hg]; abel
    | single p m =>
      obtain ⟨y, z⟩ := p
      by_cases h : y = 0
      · subst h
        have : s (Finsupp.single (0, z) m) = Finsupp.single z m := by
          ext x; simp [hs, Finsupp.single_apply]
        simp [this, Finsupp.single_apply]
      · have : s (Finsupp.single (y, z) m) = 0 := by
          ext x; simp [hs, h]
        simp [this, Finsupp.single_apply, h]
  have e : g = s f := Finsupp.ext hg
  ext q
  rw [← key f q, hf, e]
  simp

end Coordinates

section Ring

variable {X : Type*} [Zero X] {A : Type*} [Ring A]

theorem addMonoidAlgebra_coboundary_eq_iff (f : A[X × X])
    (hf : mapDomain (fun p => ((0 : X), p.1, p.2)) f - mapDomain (fun p => (p.1, p.1, p.2)) f +
      mapDomain (fun p => (p.1, p.2, p.2)) f - mapDomain (fun p => (p.1, p.2, (0 : X))) f = 0)
    (g : A[X]) :
    mapDomain (fun y => ((0 : X), y)) g - mapDomain (fun y => (y, y)) g +
      mapDomain (fun y => (y, (0 : X))) g = f ↔ ∀ x, g.coeff x = f.coeff (0, x) := by
  refine ⟨fun h x => ?_, fun h => coeff_injective
    (finsupp_two_cocycle_eq_coboundary f.coeff (congrArg coeff hf) g.coeff h)⟩
  rw [← h]
  exact (coboundary_apply_zero_left g.coeff x).symm

theorem addMonoidAlgebra_existsUnique_coboundary (f : A[X × X])
    (hf : mapDomain (fun p => ((0 : X), p.1, p.2)) f - mapDomain (fun p => (p.1, p.1, p.2)) f +
      mapDomain (fun p => (p.1, p.2, p.2)) f - mapDomain (fun p => (p.1, p.2, (0 : X))) f = 0) :
    ∃! g : A[X], mapDomain (fun y => ((0 : X), y)) g - mapDomain (fun y => (y, y)) g +
      mapDomain (fun y => (y, (0 : X))) g = f := by
  simp only [addMonoidAlgebra_coboundary_eq_iff f hf]
  exact ⟨ofCoeff (f.coeff.comapDomain (fun x => ((0 : X), x)) (Prod.mk_right_injective 0).injOn),
    fun _ => rfl, fun g hg => coeff_injective (Finsupp.ext hg)⟩

end Ring

section Tensor

variable {R : Type*} [CommRing R] {H : Type*} [Ring H] [Bialgebra R H]
variable {M : Type*} [AddCommGroup M] [Module R M]


variable {X : Type*} [AddMonoid X]


end Tensor

universe u v w

end GlobalTheory

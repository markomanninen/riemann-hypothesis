module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et

section Transfer

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

end Transfer

section Semistable

variable (O : Type) [CommRing O] (ϖ : O) (m r : ℕ)

abbrev ssModel : Type :=
  MvPolynomial (Fin m) O ⧸ Ideal.span (Set.singleton ((∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) -
      MvPolynomial.C ϖ))

theorem isStrictlySemistable_model (h1 : 1 ≤ r) (h2 : r ≤ m) :
    IsStrictlySemistable ϖ (Spec.map (CommRingCat.ofHom (algebraMap O (ssModel O ϖ m r)))) := by
  intro x
  refine ⟨⊤, isAffineOpen_top _, trivial, m, r, h1, h2, (Scheme.ΓSpecIso (CommRingCat.of (ssModel O ϖ m r))).inv.hom,
    RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _), ?_⟩
  have h : (Spec.map (CommRingCat.ofHom (algebraMap O (ssModel O ϖ m r)))).appTop =
      (Spec.map (CommRingCat.ofHom (algebraMap O (ssModel O ϖ m r)))).appLE ⊤ ⊤ le_top := Scheme.Hom.app_eq_appLE _
  rw [← h, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

end Semistable

section MuTest

end MuTest

end GlobalTheory.Et

end

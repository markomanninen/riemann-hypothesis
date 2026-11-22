module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpacePullbackAffineOpenOfIsDomainTens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibleSpace_pullback_affine_open_of_isDomain_tensor : ∀ {F : Type} [Field F] {X : Scheme.{0}} (g : X ⟶ Sp F) (V : X.Opens), IsAffineOpen V →
    ∀ (k : Type) [Field k] (f : F →+* k),
    (letI : Algebra F Γ(X, V) :=
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    letI : Algebra F k := f.toAlgebra
    IsDomain (k ⊗[F] Γ(X, V)) → IrreducibleSpace ↑(pullback (V.ι ≫ g) (spMap f))) := by
  intro F _ X g V hV k _ f
  let : Algebra F Γ(X, V) :=
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
  let : Algebra F k := f.toAlgebra
  intro hdom
  have hSpec : hV.fromSpec ≫ g = Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, V))) := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen_top _) hV le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have hComp : V.ι ≫ g = hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, V))) := by
    rw [← hSpec, IsAffineOpen.isoSpec_hom_fromSpec_assoc]
  let m := pullback.map (V.ι ≫ g) (spMap f) (Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, V))))
    (Spec.map (CommRingCat.ofHom (algebraMap F k))) hV.isoSpec.hom (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, hComp]) (by simp only [Category.comp_id, Category.id_comp]; rfl)
  let e : pullback (V.ι ≫ g) (spMap f) ≅ Spec (CommRingCat.of (Γ(X, V) ⊗[F] k)) :=
    asIso m ≪≫ pullbackSpecIso F Γ(X, V) k
  have : IsDomain (Γ(X, V) ⊗[F] k) :=
    MulEquiv.isDomain (k ⊗[F] Γ(X, V)) (Algebra.TensorProduct.comm F Γ(X, V) k).toRingEquiv.toMulEquiv
  have : IrreducibleSpace (Spec (CommRingCat.of (Γ(X, V) ⊗[F] k))) :=
    PrimeSpectrum.irreducibleSpace (R := Γ(X, V) ⊗[F] k)
  exact Function.Surjective.irreducibleSpace e.inv.homeomorph.continuous e.inv.homeomorph.surjective

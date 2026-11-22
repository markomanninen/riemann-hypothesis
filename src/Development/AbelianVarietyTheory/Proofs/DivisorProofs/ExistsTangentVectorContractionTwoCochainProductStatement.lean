module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorContractionTwoCochainProduct
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangentVector_contraction_twoCochain_product :
    ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (v : epsR R ⟶ B), IsTangent v →
    (∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (x : Pt A D),
      let y : Pt A D' := spOver φ ≫ x
      ∃ (s : trivAt (pt0 B x) ⟶ thickAt B x) (i : trivAt (ptV v x) ⟶ thickAt B x)
        (s' : trivAt (pt0 B y) ⟶ thickAt B y) (i' : trivAt (ptV v y) ⟶ thickAt B y)
        (a : trivAt (pt0 B x) ⟶ trivAt (pt0 B y)) (b : trivAt (ptV v x) ⟶ trivAt (ptV v y))
        (τ : thickAt B x ⟶ thickAt B y),
        (∀ r, s.φ r = TrivSqZeroExt.inl r) ∧ (∀ r, i.φ r = r) ∧
        (∀ r, s'.φ r = TrivSqZeroExt.inl r) ∧ (∀ r, i'.φ r = r) ∧
        (∀ r, a.φ r = φ r) ∧ (∀ r, b.φ r = epsHom φ r) ∧ (∀ r, τ.φ r = epsHom φ r)) ∧
    ∀ z : C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), ∃ κ : Fn1 A, IsContr z v κ :=
  GlobalTheory.PtExt.ContrMor.exists_contr

module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineRingHomPairOfSpecializes
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCoprimeZpow
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_ring_hom_pair_of_specializes :
    ∀ {X : Scheme.{0}} {k k' : Type} [Field k] [Field k']
      (x : Spec (CommRingCat.of k) ⟶ X) (x' : Spec (CommRingCat.of k') ⟶ X)
      (u : Spec (CommRingCat.of k)) (u' : Spec (CommRingCat.of k')),
      x'.base u' ⤳ x.base u →
      ∃ (B : Type) (_ : CommRing B) (g : B →+* k) (g' : B →+* k')
        (ρ : Spec (CommRingCat.of B) ⟶ X),
        RingHom.ker g' ≤ RingHom.ker g ∧
          Spec.map (CommRingCat.ofHom g) ≫ ρ = x ∧ Spec.map (CommRingCat.ofHom g') ≫ ρ = x' := by
  exact @GlobalTheory.exists_ringHom_pair_of_specializes

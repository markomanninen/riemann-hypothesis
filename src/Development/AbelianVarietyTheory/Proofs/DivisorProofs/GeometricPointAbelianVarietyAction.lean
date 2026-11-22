module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConjugatePullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionBySetPowOfDivisibleNumberFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIsAlgClosedStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionGeometricPointsEqPowTwoDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyAndPrimeDvdDegOfDvdNorm

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_point_abelian_variety_action : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ (B : AbVar k) (e : (Over.mk x ⟶ A) ≃* B.Pt) (ψ : 𝓞 F →+* End B), (∀ (c : 𝓞 F) (g : Over.mk x ⟶ A), e (g ≫ act.act c) = e g ≫ Hom.hom (ψ c).asHom) ∧ ∀ c : 𝓞 F, (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left → v ≫ act.act c = 1 → v = 1) → ∀ w : epsPtR (𝟙 (Sp k)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = (1 : Over.mk (𝟙 (Sp k)) ⟶ B.X).left → w ≫ Hom.hom (ψ c).asHom = 1 → w = 1 := by
  intro S A _ _ hA F _ _ act k _ _ x
  have push_comp_map {T : Over (Sp k)} {g : T.left ⟶ S} (f : A ⟶ A)
      (e : (T ⟶ (Over.pullback x).obj A) → (Over.mk g ⟶ A))
      (he : ∀ z, (e z).left = z.left ≫ pullback.fst A.hom x)
      (z : T ⟶ (Over.pullback x).obj A) :
      e (z ≫ (Over.pullback x).map f) = e z ≫ f := by
    have map_fst : ((Over.pullback x).map f).left ≫ pullback.fst A.hom x =
        pullback.fst A.hom x ≫ f.left := by
      simp only [Over.pullback_map_left, pullback.lift_fst]
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, map_fst, Category.assoc]
  have h : IsGrpPullback ((Over.pullback x).obj A) A x (pullback.fst A.hom x) := isGrpPullback_pullback A x
  have hab : IsAbelianScheme ((Over.pullback x).obj A) := GlobalTheory.isAbelianScheme_pullback_obj x A hA
  obtain ⟨g, hg⟩ := GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme k _ hab
  let B : AbVar k := { X := (Over.pullback x).obj A, ab := hab, dim := g, smooth := hg }
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (𝟙_ (Over (Sp k))) x (by simp)
  have i : ptOver k (AlgebraicClosure k) ≅ 𝟙_ (Over (Sp k)) := by
    let σ : k ≃+* AlgebraicClosure k :=
      RingEquiv.ofBijective (algebraMap k (AlgebraicClosure k))
        IsAlgClosed.algebraMap_bijective_of_isIntegral
    have : IsIso (spMap (algebraMap k (AlgebraicClosure k))) := by
      change IsIso (Spec.map σ.toCommRingCatIso.hom)
      infer_instance
    exact Over.isoMk (asIso (spMap (algebraMap k (AlgebraicClosure k)))) (by
      change spMap _ ≫ 𝟙 _ = spMap _
      exact Category.comp_id _)
  let ptEquiv : (𝟙_ (Over (Sp k)) ⟶ B.X) ≃* B.Pt :=
    { toFun := fun t => i.hom ≫ t
      invFun := fun t => i.inv ≫ t
      left_inv := fun t => by simp
      right_inv := fun t => by simp
      map_mul' := fun t u => MonObj.comp_mul _ t u }
  let e : (Over.mk x ⟶ A) ≃* B.Pt := e₀.symm.trans ptEquiv
  have hm : ∀ c, IsMonHom ((Over.pullback x).map (act.act c)) := fun c => by
    have := act.hom c; infer_instance
  let ψf : 𝓞 F → (B ⟶ B) := fun c => Hom.mk (A := B) (B := B)
    ((Over.pullback x).map (act.act c)) (h := hm c)
  have hψ : ∀ c, Hom.hom (ψf c) = (Over.pullback x).map (act.act c) := fun c => rfl
  have hom_ext {f g : B ⟶ B} (hfg : Hom.hom f = Hom.hom g) : f = g := Subtype.ext hfg
  have act0 : act.act 0 = 1 := by
    have := act.add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  let ψ : 𝓞 F →+* End B :=
    { toFun := fun c => End.of (ψf c)
      map_one' := by
        apply End.ext
        change ψf 1 = 𝟙 B
        apply hom_ext
        rw [hψ, act.one, CategoryTheory.Functor.map_id, id_hom]
      map_mul' := fun a b => by
        apply End.ext
        change ψf (a * b) = ψf b ≫ ψf a
        apply hom_ext
        rw [comp_hom, hψ, hψ, hψ, mul_comm, act.mul, CategoryTheory.Functor.map_comp]
      map_zero' := by
        apply End.ext
        change ψf 0 = 0
        apply hom_ext
        rw [hψ, act0, zero_hom]
        exact CategoryTheory.Functor.map_one _
      map_add' := fun a b => by
        apply End.ext
        change ψf (a + b) = ψf a + ψf b
        apply hom_ext
        rw [add_hom, hψ, hψ, hψ, act.add]
        exact CategoryTheory.Functor.map_mul _ _ _ }
  refine ⟨B, e, ψ, fun c z => ?_, fun c H w hw1 hw2 => ?_⟩
  · show ptEquiv (e₀.symm (z ≫ act.act c)) =
      ptEquiv (e₀.symm z) ≫ (Over.pullback x).map (act.act c)
    have : e₀.symm (z ≫ act.act c) = e₀.symm z ≫ (Over.pullback x).map (act.act c) := by
      apply e₀.injective
      rw [MulEquiv.apply_symm_apply, push_comp_map (act.act c) e₀ he₀, MulEquiv.apply_symm_apply]
    rw [this]
    rfl
  · obtain ⟨e₁, he₁⟩ := GlobalTheory.LiePull.exists_pushEquiv h (epsPtR (𝟙 (Sp k)))
      (spMap (algebraMap k (DualNumber k)) ≫ x) (by simp)
    obtain ⟨e₂, he₂⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk (𝟙 (Sp k))) x (by simp)
    have one : (1 : Over.mk x ⟶ A).left = (1 : Over.mk (𝟙 (Sp k)) ⟶ (Over.pullback x).obj A).left ≫
        pullback.fst A.hom x := by
      rw [← he₂, map_one]
    have r1 : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (e₁ w).left = (1 : Over.mk x ⟶ A).left := by
      rw [he₁, one, ← Category.assoc, hw1]
    have r2 : e₁ w ≫ act.act c = 1 := by
      rw [← push_comp_map (act.act c) e₁ he₁]
      have hw2' : w ≫ Hom.hom (ψf c) = 1 := hw2
      change e₁ (w ≫ Hom.hom (ψf c)) = 1
      rw [hw2', map_one]
    exact e₁.injective ((H (e₁ w) r1 r2).trans (map_one e₁).symm)

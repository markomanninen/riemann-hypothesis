module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteGroupHomKernelPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerKill

theorem flat_of_isFinite_field (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] (hf : IsFinite H.hom) :
    Flat H.hom := by
  have haff : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨A, ⟨e⟩⟩ := (essImage_hopfSpec (G := Grp.mk H)).2 haff
  let B : Type := A.unop
  letI : HopfAlgebra K B := A.unop.hopfAlgebra
  let G : Over (Spec (CommRingCat.of K)) :=
    (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of K))
  letI : GrpObj G := instGrpObjSpecAsOverSpec (R := CommRingCat.of K) (A := CommRingCat.of B)
  let i : G ≅ H := (Grp.forget _).mapIso e
  obtain ⟨j, hj, hw⟩ : ∃ j : Spec (CommRingCat.of B) ⟶ H.left, IsIso j ∧
      Spec.map (CommRingCat.ofHom (algebraMap K B)) = j ≫ H.hom :=
    ⟨i.hom.left, inferInstanceAs (IsIso ((Over.forget _).map i.hom)), (Over.w i.hom).symm⟩
  haveI h1 : Flat (Spec.map (CommRingCat.ofHom (algebraMap K B))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  have e : H.hom = inv j ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) := by
    rw [hw, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

theorem kernel_killed : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsFinite f.hom.left →
    ∃ n : ℕ, 0 < n ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1 := by
  intro K _ A B f hf
  let H := pullback f.hom η[B.X]
  let i : H ⟶ A.X := pullback.fst _ _
  have hp : IsPullback i (toUnit H) f.hom η[B.X] := by
    rw [toUnit_unique (toUnit _) (pullback.snd f.hom η[B.X])]
    exact IsPullback.of_hasPullback _ _
  haveI : Mono i := ⟨fun _ _ e => hp.hom_ext e (toUnit_unique _ _)⟩
  let lift {W : Over (Sp K)} (g : W ⟶ A.X) (hg : g ≫ f.hom = 1) : W ⟶ H :=
    GlobalTheory.CompanionTheory.KerPull.Kernel.kerLift hp g hg
  have lift_comp {W : Over (Sp K)} (g : W ⟶ A.X) (hg : g ≫ f.hom = 1) :
      lift g hg ≫ i = g := GlobalTheory.CompanionTheory.KerPull.Kernel.kerLift_comp hp g hg
  have kills (W : Over (Sp K)) (x : W ⟶ H) : (x ≫ i) ≫ f.hom = 1 := by
    rw [Category.assoc, hp.w, ← Category.assoc, toUnit_unique (x ≫ toUnit H) (toUnit W), Hom.one_def]
  letI : GrpObj H :=
    { one := lift η[A.X] (by rw [IsMonHom.one_hom, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp])
      mul := lift (fst H H ≫ i * snd H H ≫ i) (by
        rw [MonObj.mul_comp, kills, kills, _root_.mul_one])
      inv := lift (i ≫ ι[A.X]) (by
        have e : i ≫ f.hom = 1 := by simpa using kills H (𝟙 H)
        have h : (i⁻¹ * i) ≫ f.hom = 1 := by rw [inv_mul_cancel, MonObj.one_comp]
        rw [MonObj.mul_comp, e, _root_.mul_one] at h
        exact h)
      one_mul := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        rw [toUnit_unique (fst (𝟙_ (Over (Sp K))) H) (toUnit _), ← Hom.one_def, _root_.one_mul, leftUnitor_hom]
      mul_one := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        rw [toUnit_unique (snd H (𝟙_ (Over (Sp K)))) (toUnit _), ← Hom.one_def, _root_.mul_one, rightUnitor_hom]
      mul_assoc := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        exact _root_.mul_assoc _ _ _
      left_inv := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        rw [← Hom.one_def]
        exact inv_mul_cancel i
      right_inv := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, lift, lift_comp]
        rw [← Hom.one_def]
        exact mul_inv_cancel i }
  haveI : IsMonHom i := by
    refine { one_hom := lift_comp _ _, mul_hom := ?_ }
    refine (lift_comp _ _).trans ?_
    rw [Hom.mul_def]
    simp
  haveI : IsCommMonObj A.X := A.ab.comm
  haveI : IsCommMonObj H := by
    refine (isCommMonObj_iff_isMulCommutative _).mpr fun T => ⟨⟨fun x y => ?_⟩⟩
    rw [← cancel_mono i, MonObj.mul_comp, MonObj.mul_comp, mul_comm]
  have hHf : IsFinite H.hom := by
    have hl := hp.map (Over.forget _)
    have h1 : IsFinite (toUnit H).left := MorphismProperty.of_isPullback (P := @IsFinite) hl hf
    have h2 : H.hom = (toUnit H).left ≫ (𝟙_ (Over (Sp K))).hom := (Over.w _).symm
    rw [h2]
    exact inferInstanceAs (IsFinite (_ ≫ 𝟙 _))
  have hfl : Flat H.hom := flat_of_isFinite_field K H hHf
  obtain ⟨N, hN, h⟩ := GlobalTheory.FiniteFlatKilled.main K H hHf hfl
  refine ⟨N, hN, fun T x hx => ?_⟩
  obtain ⟨y, rfl⟩ : ∃ y : T ⟶ H, y ≫ i = x := ⟨_, GlobalTheory.CompanionTheory.KerPull.Kernel.kerLift_comp hp x hx⟩
  rw [← MonObj.comp_pow, ← Category.id_comp i,
    ← MonObj.pow_comp, h, MonObj.one_comp, MonObj.comp_one]

end GlobalTheory.AV.KerKill

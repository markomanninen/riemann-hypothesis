module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionGenericFibre
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Formalism.SharpRestriction.Divisibility.LatticeTransfer
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsWeilChar
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
public import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationPrimitiveRootPrimePowSubOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedCubicalSymmetricExtensionNormalB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalExtendsAndExtendGen

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIntegral

theorem triv_theta (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) : AbLaw.Triv (Theta A L) := by
  obtain ⟨t, ht⟩ := hC S A hA L hL (G3 A) (x3 A 0) (x3 A 1) (x3 A 2)
  have e : lift (x3 A 0) (lift (x3 A 1) (x3 A 2)) = 𝟙 (G3 A) := by
    ext <;> simp [x3]
  obtain ⟨t', ht', -⟩ := exists_gen hL (φ' := thφ A (x3 A)) (ε' := thε) (fun V _ k => by
    have h := prod_cub (x3 A 0) (x3 A 1) (x3 A 2) k
    rw [e] at h
    refine Eq.trans ?_ (h.symm.trans (Finset.prod_congr rfl fun I _ =>
      congrArg (fun q => k q ^ thε I) (Category.id_comp _)))
    simp [Fin.prod_univ_eight]) t ht
  exact ⟨t', ht'⟩

theorem isGrpPullback_prod {S S' : Scheme.{0}} {A B : Over S} {A' B' : Over S'} [GrpObj A] [GrpObj B]
    [GrpObj A'] [GrpObj B'] {b : S' ⟶ S} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    (m : IsGrpPullback A' A b f) (n : IsGrpPullback B' B b g) {h : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) :
    IsGrpPullback (A' ⊗ B') (A ⊗ B) b h := by
  refine ⟨isPullback_prod m.1 n.1 h₁ h₂, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (grpMor_prod (κ := dp0 ℤ) (κ' := dp0 ℤ) (σ := RingHom.id ℤ) (t := specZIsTerminal.from _) (t' := specZIsTerminal.from _)
    ⟨Cris.isDPMorphism_of_eq_bot _ rfl _ _, specZIsTerminal.hom_ext _ _, m.1.w, m.2⟩
    ⟨Cris.isDPMorphism_of_eq_bot _ rfl _ _, specZIsTerminal.hom_ext _ _, n.1.w, n.2⟩ h₁ h₂).mul T x y x₀ y₀ hx hy

theorem lift_left_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}
    {h : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h₁ : h ≫ (fst G G).left = (fst G' G').left ≫ φ)
    (h₂ : h ≫ (snd G G).left = (snd G' G').left ≫ φ) {T : Over S} {T' : Over S'} (τ : T'.left ⟶ T.left)
    {x y : T ⟶ G} {x' y' : T' ⟶ G'} (hx : x'.left ≫ φ = τ ≫ x.left) (hy : y'.left ≫ φ = τ ≫ y.left) :
    (lift x' y').left ≫ h = τ ≫ (lift x y).left := by
  have p : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  apply p.hom_ext
  · rw [Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, lift_fst, hx, Category.assoc, ← Over.comp_left,
      lift_fst]
  · rw [Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, lift_snd, hy, Category.assoc, ← Over.comp_left,
      lift_snd]

theorem one_left_comm {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) {T : Over S} {T' : Over S'} (τ : T'.left ⟶ T.left)
    (hτ : τ ≫ T.hom = T'.hom ≫ f) : (1 : T' ⟶ G').left ≫ φ = τ ≫ (1 : T ⟶ G).left := by
  let σ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk τ hτ
  exact congrArg (fun q => q.left) ((map_one (pushHom hp T')).trans (MonObj.comp_one σ).symm)

theorem lift_pow {S : Scheme.{0}} {G : Over S} [GrpObj G] {T : Over S} {x y : T ⟶ G} {N : ℕ} (hx : x ^ N = 1)
    (hy : y ^ N = 1) : lift x y ^ N = 1 := by
  ext1 <;> simp only [MonObj.pow_comp, MonObj.one_comp, lift_fst, lift_snd, hx, hy]

section Algebra

variable {R K : Type} [CommRing R] [CommRing K] [Algebra R K] (B : Type) [CommRing B]

def twoMap [Algebra R B] : B ⊗[R] B →ₐ[R] (K ⊗[R] B) ⊗[K] (K ⊗[R] B) :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft (S := R)).comp Algebra.TensorProduct.includeRight)
    (((Algebra.TensorProduct.includeRight (R := K)).restrictScalars R).comp Algebra.TensorProduct.includeRight)
    fun _ _ => .all _ _

theorem twoMap_tmul [Algebra R B] (a b : B) :
    twoMap (K := K) B (a ⊗ₜ[R] b) = ((1 : K) ⊗ₜ[R] a) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] b) := by
  simp [twoMap]

variable {B} [Bialgebra R B] [Module.Finite R B] [Module.Projective R B]

theorem contract_twoMap (χ : CartierDual R B) (u : B ⊗[R] B) :
    TensorProduct.rid K _ ((CartierDual.baseChange R K B ((1 : K) ⊗ₜ χ)).ofConv.lTensor _ (twoMap (K := K) B u)) =
      (1 : K) ⊗ₜ[R] TensorProduct.rid R _ (χ.ofConv.lTensor _ u) := by
  induction u with
  | add x y hx hy => simp only [map_add (f := _), hx, hy, tmul_add]
  | tmul a b =>
    have := CartierDual.baseChange_tmul_tmul K 1 1 χ b
    rw [twoMap_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, rid_tmul, rid_tmul]
    rw [show (CartierDual.baseChange R K B ((1 : K) ⊗ₜ χ)).ofConv ((1 : K) ⊗ₜ b) = χ.ofConv b • (1 * 1 : K) from this,
      _root_.mul_one, smul_assoc, one_smul, tmul_smul]

end Algebra

section Level

variable {p : ℕ} {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {Γ : PDivGroup p R} {𝒜 : PDivGroup p K}

end Level

end GlobalTheory.WeilIntegral

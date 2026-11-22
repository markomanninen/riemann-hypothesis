module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfBijectiveAffinePts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi (mulN)

namespace GlobalTheory.AVTower

theorem finrank_torsion {k : Type} [Field k] (A : AbVar k) {N : ℕ} (hN : N ≠ 0)
    {S : Type} [CommRing S] [Algebra k S] [Module.Finite k S] (y : SpAlg k S ⟶ A.X)
    (h : IsPullback y.left (spMap (algebraMap k S)) (mulN A.X N).left η[A.X].left) :
    Module.finrank k S = N ^ (2 * A.dim) := by
  obtain ⟨hi, hd⟩ := GlobalTheory.MulIsogeny.mul_isogeny k A (N : ℤ) (by exact_mod_cast hN)
  obtain ⟨-, hfl, -, hrk⟩ := GlobalTheory.AV.AbVar.isogeny_flat_finrank k A A _ hi
  have hf : IsFinite ((N : ℤ) • 𝟙 A).hom.left := hi.1
  have e : ((N : ℤ) • 𝟙 A).hom = mulN A.X N := by
    rw [zsmul_hom, id_hom, GrpTangent.mulN_eq_pow, zpow_natCast]
  rw [e] at hf hfl hrk
  have h2 := Scheme.Hom.finrank_of_isPullback _ _ _ _ h (⊥ : PrimeSpectrum k)
  rw [hrk, hd, Int.natAbs_natCast] at h2
  rw [← h2, spMap, Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  rfl

theorem exists_tower (p : ℕ) [hp : Fact p.Prime] (k : Type) [Field k] (A : AbVar k) :
    ∃ G : PDivGroup p k, G.height = 2 * A.dim ∧ Nonempty (G.TorsionTower A.X) := by
  have := A.ab.comm
  have hN : ∀ n : ℕ, 1 ≤ p ^ n := fun n => Nat.one_le_pow _ _ hp.out.pos
  choose R _ _ y h1 h2 H using fun n : ℕ => AbelianPDiv.exists_isPullback (A := A.X) A.ab (hN n)
  have h : ∀ n, AbelianPDiv.IsUnivTorsion (p ^ n) (y n) :=
    fun n => AbelianPDiv.isUnivTorsion_of_isPullback (y n) (H n)
  have hr : ∀ n (q : PrimeSpectrum k), Module.rankAtStalk (R n) q = (p ^ n) ^ (2 * A.dim) := fun n q => by
    rw [Module.rankAtStalk_eq_finrank_of_free]
    exact finrank_torsion A (pow_ne_zero _ hp.out.ne_zero) (y n) (H n)
  have hex : ∀ n : ℕ, letI := (h n).hopfAlgebra
      letI := (h (n + 1)).hopfAlgebra
      haveI := (h (n + 1)).isCocomm
      ∃ r : R (n + 1) →ₐc[k] R n, Function.Surjective r ∧
        RingHom.ker r = torsionIdeal (R := k) (A := R (n + 1)) (p ^ n) ∧
        DeRham.spOver (r : R (n + 1) →ₐ[k] R n) ≫ y (n + 1) = y n := fun n => by
    let O := k
    let S := R (n + 1)
    let R₀ := R n
    let x := y (n + 1)
    let y₀ := y n
    let N := p ^ n
    have h₀ : AbelianPDiv.IsUnivTorsion N y₀ := h n
    have h' : AbelianPDiv.IsUnivTorsion (p ^ (n + 1)) x := h (n + 1)
    have hy : y₀ ^ (p ^ (n + 1)) = 1 := by rw [pow_succ, pow_mul, h₀.1, one_pow]
    let _ := h₀.hopfAlgebra
    let _ := h'.hopfAlgebra
    have := h'.isCocomm
    let r := h'.lift y₀ hy
    have hr : DeRham.spOver r ≫ x = y₀ := h'.lift_y _ _
    have hc : ∀ {C : Type} [CommRing C] [Algebra O C] (f : R₀ →ₐ[O] C), DeRham.spOver (f.comp r) ≫ x = DeRham.spOver f ≫ y₀ :=
      fun f => h'.comp_lift_y f _ _
    have ht : ∀ {C : Type} [CommRing C] [Algebra O C] (f : S →ₐ[O] C),
        torsionIdeal (R := O) (A := S) N ≤ RingHom.ker f ↔ (DeRham.spOver f ≫ x) ^ N = 1 := fun {C} _ _ f => by
      rw [torsionIdeal_le_ker_iff, ← WithConv.ofConv_toConv f, ← h'.pow_y, WithConv.ofConv_toConv,
        ← h'.counitMap_y (Algebra.ofId O C)]
      exact ⟨fun e => by rw [e]; rfl, fun e => WithConv.ofConv_injective (h'.inj e)⟩
    let π := Ideal.Quotient.mkₐ O (torsionIdeal (R := O) (A := S) N)
    have hπ := (ht π).1 fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
    let s := h₀.lift _ hπ
    have hs : s.comp r = π := h'.inj ((hc s).trans (h₀.lift_y _ _))
    have hk : torsionIdeal (R := O) (A := S) N ≤ RingHom.ker r := (ht r).2 (by rw [hr, h₀.1])
    let r' : (S ⧸ torsionIdeal (R := O) (A := S) N) →ₐ[O] R₀ := Ideal.Quotient.liftₐ _ r hk
    have hr' : r'.comp π = r := Ideal.Quotient.liftₐ_comp _ _ _
    have hs' : r'.comp s = AlgHom.id O R₀ := h₀.inj (by
      rw [h₀.comp_lift_y, ← Category.assoc, DeRham.spOver_comp, hr', hr, PDiv.spOver_id, Category.id_comp])
    refine ⟨.ofAlgHom r (h'.inj ?_) (h'.inj ?_), fun b => ?_, le_antisymm (fun a ha => ?_) hk, hr⟩
    · exact (hc _).trans ((h₀.counitMap_y (AlgHom.id O O)).trans (h'.counitMap_y (AlgHom.id O O)).symm)
    · refine (h'.comulMap_y' _ (Algebra.TensorProduct.includeLeft.comp r)
        (Algebra.TensorProduct.includeRight.comp r) (fun a => by simp) (fun a => by simp)).trans ?_
      rw [hc, hc, hc]
      exact (h₀.comulMap_y (AlgHom.id O _)).symm
    · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (s b)
      refine ⟨a, (DFunLike.congr_fun hr' a).symm.trans ?_⟩
      exact (congrArg r' ha).trans (DFunLike.congr_fun hs' b)
    · have ha' : r a = 0 := ha
      have : π a = 0 := by rw [← hs, AlgHom.comp_apply, ha', map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
  choose r r1 r2 r3 using hex
  let G : PDivGroup p k :=
    { height := 2 * A.dim
      A := R
      hopf := fun n => (h n).hopfAlgebra
      cocomm := fun n => (h n).isCocomm
      finite := h1
      projective := h2
      rank_eq := fun n q => (hr n q).trans (pow_mul _ _ _).symm
      res := r
      res_surjective := r1
      ker_res := r2 }
  exact ⟨G, rfl, ⟨{
    y := y
    mul := fun n B _ _ => (h n).mul_y
    inj := fun n B _ _ _ _ => (h n).inj
    surj := fun n B _ _ z hz => ((h n).2 B z hz).exists
    res := r3 }⟩⟩

theorem height_eq {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] (A : AbVar k) (G : PDivGroup p k)
    (t : G.TorsionTower A.X) : G.height = 2 * A.dim := by
  have P := (TorsionTower.isPullback_y p k G A.X t 1).map (Over.forget _)
  have e : (toUnit (SpAlg k (G.A 1))).left = spMap (algebraMap k (G.A 1)) := by
    simpa using Over.w (toUnit (SpAlg k (G.A 1)))
  simp only [Over.forget_map] at P
  rw [e] at P
  have hf := finrank_torsion A (pow_ne_zero 1 hp.out.ne_zero) (t.y 1) P
  have hr := G.rank_eq 1 ⊥
  rw [Module.rankAtStalk_eq_finrank_of_free] at hr
  change Module.finrank k (G.A 1) = _ at hr
  rw [hf, pow_one, Nat.one_mul] at hr
  exact (Nat.pow_right_injective hp.out.two_le hr).symm

theorem exists_tower_and_height_eq : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A : AbVar k),
    (∃ G : PDivGroup p k, Nonempty (G.TorsionTower A.X)) ∧
      ∀ (G : PDivGroup p k) (t : G.TorsionTower A.X), G.height = 2 * A.dim := by
  intro p _ k _ A
  obtain ⟨G, -, hG⟩ := exists_tower p k A
  exact ⟨⟨G, hG⟩, fun G t => height_eq A G t⟩

end GlobalTheory.AVTower

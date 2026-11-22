module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormNatAbsEqMinpolyCoeffZeroPow
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.OActDeg

def endHom {k : Type} [Field k] (X : GlobalTheory.AV.AbVar k) (F : Type) [Field F] [NumberField F] (ρ : OAct (𝓞 F) X.X) :
    𝓞 F →+* CategoryTheory.End X where
  toFun c := End.of (GlobalTheory.AV.AbVar.Hom.mk (A := X) (B := X) (ρ.act c) (h := ρ.hom c))
  map_one' := by
    refine End.ext (Subtype.ext ?_)
    exact ρ.one
  map_mul' a b := by
    refine End.ext (Subtype.ext ?_)
    change ρ.act (a * b) = ρ.act b ≫ ρ.act a
    rw [mul_comm, ρ.mul]
  map_zero' := by
    refine End.ext (Subtype.ext ?_)
    change ρ.act 0 = 1
    have h := ρ.add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  map_add' a b := by
    refine End.ext (Subtype.ext ?_)
    exact ρ.add a b

open Polynomial GlobalTheory.AV.AbVar in
theorem isFinite_and_finrank_eq_norm_pow : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
    ∀ (F : Type) [Field F] [NumberField F] (ρ : OAct (𝓞 F) A) (l d : ℕ), l.Prime → (l : k) ≠ 0 →
    Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ l = 1} = l ^ (d * Module.finrank ℚ F) →
    ∀ c : 𝓞 F, c ≠ 0 → IsFinite (ρ.act c).left ∧
      (ρ.act c).left.finrank ((1 : Over.mk (𝟙 (Sp k)) ⟶ A).left (IsLocalRing.closedPoint k)) =
        (Algebra.norm ℤ c).natAbs ^ d := by
  intro k _ _ A _ hA F _ _ ρ l d hl hl0 hcard c hc
  let X : GlobalTheory.AV.AbVar k := GlobalTheory.TateHondaBridge.toAbVar A hA
  have h2 := GlobalTheory.abMulN_holds k A X.dim l hA X.smooth hl0
  rw [hcard] at h2
  have hdim : 2 * X.dim = d * Module.finrank ℚ F :=
    (Nat.pow_right_injective hl.two_le h2).symm
  let actionHom := endHom X F ρ
  let f := actionHom c
  let m := minpoly ℤ c
  have hi : IsIntegral ℤ c := NumberField.RingOfIntegers.isIntegral c
  have hm : m.Monic := minpoly.monic hi
  have hp : Prime m := (minpoly.irreducible hi).prime
  have hf : aeval f m = 0 := by
    have h := Polynomial.hom_eval₂ m (algebraMap ℤ (𝓞 F)) actionHom c
    rw [← aeval_def, show aeval c m = 0 from minpoly.aeval ℤ c, map_zero,
      Subsingleton.elim (actionHom.comp (algebraMap ℤ (𝓞 F))) (algebraMap ℤ _), ← aeval_def] at h
    exact h.symm
  have ⟨e, he, hdeg⟩ : ∃ e : ℕ, e * m.natDegree = 2 * X.dim ∧
      (deg f.asHom : ℤ) = m.coeff 0 ^ e := by
    have : Fact l.Prime := ⟨hl⟩
    obtain ⟨-, -, -, hfin, hrank⟩ := tl_free_finrank k l hl0 X
    have hchar (g : End X) :
        (charpoly g).map (algebraMap ℤ ℚ_[l]) = (vmap l g.asHom).charpoly := by
      obtain ⟨⟨hmonic, hdegree, heval⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec k X g
      have h := GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate
        k l hl0 X g ((charpoly g).map (algebraMap ℤ ℚ)) (hmonic.map _)
        (by rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)), hdegree])
        (fun n => by simpa using congrArg (algebraMap ℤ ℚ) (heval n))
      rw [← h, Polynomial.map_map,
        show (algebraMap ℚ ℚ_[l]).comp (algebraMap ℤ ℚ) = algebraMap ℤ ℚ_[l] from Subsingleton.elim _ _]
    have hdet : LinearMap.det (vmap l f.asHom) = (deg f.asHom : ℚ_[l]) := by
      have hneg : (-f).asHom = -f.asHom := map_neg (End.addEquiv (X := X)) f
      have hv : vmap l f.asHom = (-1 : ℚ_[l]) • vmap l (-f).asHom := by
        simp only [hneg, vmap, map_neg, LinearMap.baseChange_neg, neg_one_smul, neg_neg]
      have hev := (GlobalTheory.T.abelianVarietyEndCharpoly_spec k X (-f)).1.2.2 0
      rw [Int.cast_zero, zero_sub, neg_neg] at hev
      rw [hv, LinearMap.det_smul, LinearMap.det_eq_sign_charpoly_coeff, ← hchar (-f),
        Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero, hev, hrank, pow_mul, neg_one_sq, one_pow]
      simp
    have hinj : Function.Injective (algebraMap ℤ ℚ_[l]) := RingHom.injective_int _
    let ψ : End X →+* Module.End ℚ_[l] (Vl l X) :=
      (Module.End.baseChangeHom ℤ_[l] ℚ_[l] (Tl l X)).toRingHom.comp (tend l X)
    have hT : aeval (vmap l f.asHom) m = 0 := by
      change aeval (ψ f) m = 0
      have h := Polynomial.hom_eval₂ m (algebraMap ℤ (End X)) ψ f
      rw [← aeval_def, hf, map_zero,
        Subsingleton.elim (ψ.comp (algebraMap ℤ (End X))) (algebraMap ℤ _), ← aeval_def] at h
      exact h.symm
    have hdvd := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank (vmap l f.asHom) (m.map (algebraMap ℤ ℚ_[l]))
      (by rw [aeval_map_algebraMap]; exact hT)
    rw [← hchar f, ← Polynomial.map_pow] at hdvd
    obtain ⟨⟨hmonic, hdegree, -⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec k X f
    rw [Polynomial.map_dvd_map _ hinj hmonic] at hdvd
    obtain ⟨i, -, hassociated⟩ := (dvd_prime_pow hp _).1 hdvd
    have hpow : charpoly f = m ^ i := Polynomial.eq_of_monic_of_associated hmonic (hm.pow i) hassociated
    refine ⟨i, ?_, ?_⟩
    · rw [← hdegree, hpow, hm.natDegree_pow]
    · have h := LinearMap.det_eq_sign_charpoly_coeff (vmap l f.asHom)
      rw [hdet, ← hchar f, coeff_map, hrank, pow_mul, neg_one_sq, one_pow, _root_.one_mul, hpow,
        coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero] at h
      apply Int.cast_injective (α := ℚ_[l])
      rw [Int.cast_natCast, h, eq_intCast, Int.cast_pow]
  obtain ⟨r, hr, hnorm⟩ := norm_natAbs_eq_minpoly_coeff_zero_pow c
  have hpos : 0 < m.natDegree := minpoly.natDegree_pos hi
  have her : e = d * r := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [he, hdim, ← hr, _root_.mul_assoc]
  have hdeg' : deg f.asHom = (m.coeff 0).natAbs ^ e := by
    have h := congrArg Int.natAbs hdeg
    rwa [Int.natAbs_natCast, Int.natAbs_pow] at h
  have hval : deg f.asHom = (Algebra.norm ℤ c).natAbs ^ d := by
    rw [hdeg', hnorm, ← pow_mul, her, mul_comm]
  have hiso : IsIsogeny f.asHom := by
    classical
    by_contra h
    have hzero : deg f.asHom = 0 := by rw [deg, ite_eq_right h]
    rw [hdeg'] at hzero
    exact minpoly_int_coeff_zero_ne_zero c hc (Int.natAbs_eq_zero.1 (pow_eq_zero_iff'.1 hzero).1)
  refine ⟨hiso.1, ?_⟩
  classical
  rw [← hval]
  unfold GlobalTheory.AV.AbVar.deg
  rw [ite_eq_left hiso]
  rfl

end GlobalTheory.AV.OActDeg

end

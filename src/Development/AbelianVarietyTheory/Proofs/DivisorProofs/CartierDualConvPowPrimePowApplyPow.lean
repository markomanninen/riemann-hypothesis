module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse

@[expose] public section

open TensorProduct Coalgebra Bialgebra WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory

namespace PDivGroup

theorem convPow_prime_apply_pow_prime (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n) :
    (χ ^ p) (a ^ p) = χ (mulBy R (G.A n) p a) ^ p := by
  let A := G.A n
  let S := ULift.{0} R
  let σ : R →+* S := ULift.ringEquiv.symm.toRingHom.comp (frobRing h)
  let : Algebra R S := σ.toAlgebra
  let : Module R S := Algebra.toModule
  let : SMul R S := Algebra.toSMul
  have hA : (p : A) = 0 := natCast_eq_zero_of_algebra h A
  -- With Frobenius acting on the target scalars, precomposition by the pth power is linear.
  let pullPow (φ : CartierDual R A) : WithConv (A →ₗ[R] S) := toConv
    { toFun := fun x => ULift.up (φ (x ^ p))
      map_add' := fun x y => by
        change ULift.up (φ.ofConv ((x + y) ^ p)) =
          ULift.up (φ.ofConv (x ^ p) + φ.ofConv (y ^ p))
        rw [← frobRing_apply hA (x + y), map_add, map_add, frobRing_apply, frobRing_apply]
      map_smul' := fun r x => by
        change ULift.up (φ.ofConv ((r • x) ^ p)) = r • ULift.up (φ.ofConv (x ^ p))
        rw [smul_pow, φ.ofConv.map_smul, Algebra.smul_def (R := R) (A := S)]
        change ULift.up (r ^ p * φ.ofConv (x ^ p)) =
          ULift.up (frobRing h r * φ.ofConv (x ^ p))
        rw [frobRing_apply] }
  let pull : CartierDual R A →* WithConv (A →ₗ[R] S) :=
    { toFun := pullPow
      map_one' := WithConv.ext (LinearMap.ext fun x => by
        change ULift.up ((1 : CartierDual R A) (x ^ p)) = (1 : WithConv (A →ₗ[R] S)) x
        rw [LinearMap.convOne_apply, LinearMap.convOne_apply, counit_pow]
        change ULift.up (counit (R := R) x ^ p) = ULift.up (frobRing h (counit x))
        rw [frobRing_apply])
      map_mul' := fun φ ψ => WithConv.ext (LinearMap.ext fun x => by
        let d := Coalgebra.Repr.arbitrary R x
        let dPow : Coalgebra.Repr R (x ^ p) (A × A) :=
          ⟨d.index, fun i => d.left i ^ p, fun i => d.right i ^ p, by
            rw [comul_pow, ← d.eq,
              ← frobRing_apply (natCast_eq_zero_of_algebra h (A ⊗[R] A)), map_sum]
            simp only [frobRing_apply, Algebra.TensorProduct.tmul_pow]⟩
        change ULift.up ((φ * ψ) (x ^ p)) = (pullPow φ * pullPow ψ) x
        rw [dPow.convMul_apply, d.convMul_apply]
        exact map_sum ULift.ringEquiv.symm (fun i => φ (d.left i ^ p) * ψ (d.right i ^ p)) d.index) }
  obtain ⟨s, hs⟩ := exists_dualSystem R A
  have hmul : mulBy R A p a = ∑ i ∈ s, (i.1 ^ p) a • i.2 ^ p := by
    have he := BialgHom.toLinearMap_convPow (toConv (BialgHom.id R A)) p
    exact (congrArg (fun f : WithConv (A →ₗ[R] A) => f a) he).trans
      (convPow_prime_apply h s Prod.fst Prod.snd LinearMap.id (fun x => (hs x).symm) a)
  let f := (pull χ).ofConv
  have hf (x : A) : f x = ∑ i ∈ s, i.1 x • f i.2 := by
    simpa only [map_sum, map_smul] using congrArg f (hs x).symm
  let g : A →ₗ[R] S := (Algebra.linearMap R S).comp χ.ofConv
  have hg (x : A) : f x ^ p = g (x ^ p) := by
    change ULift.up (χ (x ^ p) ^ p) = ULift.up (frobRing h (χ (x ^ p)))
    rw [frobRing_apply]
  have e : pull (χ ^ p) a = g (mulBy R A p a) := by
    rw [map_pow]
    change (toConv f ^ p) a = _
    rw [convPow_prime_apply h s Prod.fst (fun i => f i.2) f hf a, hmul, map_sum]
    simp only [map_smul, hg]
  exact (congrArg ULift.down e).trans (frobRing_apply h _)

theorem convPow_primePow_apply_pow (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n r : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n) :
    (χ ^ p ^ r) (a ^ p ^ r) = χ (mulBy R (G.A n) (p ^ r) a) ^ p ^ r := by
  induction r generalizing a with
  | zero =>
    simp only [pow_zero, pow_one]
    rw [mulBy, pow_one]
    rfl
  | succ r ih =>
    rw [pow_succ, pow_mul, pow_mul, convPow_prime_apply_pow_prime p R h G n, map_pow, ih,
      mulBy_mulBy, ← pow_mul, mul_comm (p ^ r) p, ← pow_succ']

end PDivGroup

end GlobalTheory

module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.PadicActionConstInjective

@[expose] public section

set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra CategoryTheory

namespace GlobalTheory

namespace PDiv

section Lift

variable {R R' M N : Type} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R' N]

def liftSemi (f : M →ₛₗ[algebraMap R R'] N) : R' ⊗[R] M →ₗ[R'] N :=
  letI : Module R N := Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' N := ⟨fun a b w => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  LinearMap.liftBaseChange R'
    { toFun := f, map_add' := map_add f, map_smul' := fun r m => map_smulₛₗ f r m }

@[simp] theorem liftSemi_tmul (f : M →ₛₗ[algebraMap R R'] N) (r : R') (m : M) :
    liftSemi f (r ⊗ₜ m) = r • f m := rfl

end Lift

section Level

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {A A' : Type} [CommRing A]
  [Bialgebra R A] [CommRing A'] [Bialgebra R' A']

def SemiBialgHom.prim (f : SemiBialgHom σ A A') :
    LinearMap.ker (cobOne R A) →ₛₗ[σ] LinearMap.ker (cobOne R' A') where
  toFun b := ⟨f b.1, by
    have hb : cobOne R A b.1 = 0 := b.2
    have hone : SemiBialgHom.lin f 1 = 1 := f.toRingHom.map_one
    have h := congrArg (SemiBialgHom.two f) hb
    simpa only [LinearMap.mem_ker, cobOne_apply, map_sub, SemiBialgHom.two_comul,
      TensorProduct.map_tmul, hone, SemiBialgHom.lin_apply, map_zero] using h⟩
  map_add' _ _ := Subtype.ext (f.toRingHom.map_add _ _)
  map_smul' _ _ := Subtype.ext (f.smul_map _ _)

@[simp] theorem SemiBialgHom.prim_val (f : SemiBialgHom σ A A') (b : LinearMap.ker (cobOne R A)) :
    (f.prim b).1 = f b.1 := rfl

theorem isPrimitiveElem_of_mem_ker {b : A} (hb : b ∈ LinearMap.ker (cobOne R A)) :
    IsPrimitiveElem R b := by
  rw [LinearMap.mem_ker, cobOne_apply, sub_sub, sub_eq_zero] at hb
  exact hb

theorem evalAt_mul [Module.Finite R A] [Module.Projective R A] [IsCocomm R A]
    (b : LinearMap.ker (cobOne R A)) (φ ψ : CartierDual R A) :
    CartierDual.evalAt R A b.1 (φ * ψ) =
      counitAlgHom R (CartierDual R A) φ • CartierDual.evalAt R A b.1 ψ +
        counitAlgHom R (CartierDual R A) ψ • CartierDual.evalAt R A b.1 φ :=
  (CartierDual.isPrimitiveElem_iff_mul b.1).1 (isPrimitiveElem_of_mem_ker b.2) φ ψ


variable (R A) in
def primTangent [Module.Finite R A] [Module.Projective R A] [IsCocomm R A] :
    LinearMap.ker (cobOne R A) →ₗ[R] Module.Dual R (Cot R (CartierDual R A)) where
  toFun b := AugCot.lift _ (CartierDual.evalAt R A b.1) (evalAt_mul b)
  map_add' b b' := AugCot.hom_ext fun φ => by simp
  map_smul' r b := AugCot.hom_ext fun φ => by simp

@[simp] theorem primTangent_d [Module.Finite R A] [Module.Projective R A] [IsCocomm R A]
    (b : LinearMap.ker (cobOne R A)) (φ : CartierDual R A) :
    primTangent R A b (dUnit (R := R) φ) = φ b.1 := AugCot.lift_d _ _ (evalAt_mul b) φ

variable [IsCocomm R A] [IsCocomm R' A']




end Level

end PDiv

namespace PDivGroup

open PDiv

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

def resOne (n : ℕ) : G.A (n + 1) →ₐc[R] G.A 1 :=
  Nat.rec (motive := fun n => G.A (n + 1) →ₐc[R] G.A 1) (BialgHom.id R _)
    (fun n f => f.comp (G.res (n + 1))) n

@[simp] theorem resOne_zero (a : G.A 1) : G.resOne 0 a = a := rfl

@[simp] theorem resOne_succ (n : ℕ) (a : G.A (n + 2)) :
    G.resOne (n + 1) a = G.resOne n (G.res (n + 1) a) := rfl

theorem resOne_surjective (n : ℕ) : Function.Surjective (G.resOne n) := by
  induction n with
  | zero => exact Function.surjective_id
  | succ n ih => exact ih.comp (G.res_surjective (n + 1))

theorem resOne_funs (B : G.funs) (n : ℕ) : G.resOne n (B.1 (n + 1)) = B.1 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [resOne_succ, B.2, ih]

theorem resOne_mulBy (n : ℕ) (a : G.A (n + 1)) :
    G.resOne n (mulBy R _ p a) = algebraMap R _ (counit a) := by
  have h := G.mulBy_pow_self 1 (G.resOne n a)
  rw [pow_one, CoalgHomClass.counit_comp_apply] at h
  rw [map_mulBy, h]

theorem resOne_mulP (n : ℕ) (a : G.A n) :
    G.resOne n (G.mulP n a) = algebraMap R _ (counit a) := by
  obtain ⟨b, rfl⟩ := G.res_surjective n a
  rw [mulP_res, resOne_mulBy, CoalgHomClass.counit_comp_apply]

def transl (n : ℕ) : G.A (n + 1) →ₐ[R] G.A (n + 1) ⊗[R] G.A 1 :=
  (Algebra.TensorProduct.map (AlgHom.id R _) (G.resOne n : G.A (n + 1) →ₐ[R] G.A 1)).comp
    (comulAlgHom R _)

theorem transl_apply (n : ℕ) (a : G.A (n + 1)) :
    G.transl n a = (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1).lTensor _ (comul a) := rfl

theorem transl_res (n : ℕ) (a : G.A (n + 2)) :
    G.transl n (G.res (n + 1) a) =
      (G.res (n + 1) : G.A (n + 2) →ₗ[R] G.A (n + 1)).rTensor _ (G.transl (n + 1) a) := by
  rw [transl_apply, transl_apply, ← pullTwo_comul]
  generalize comul (R := R) a = t
  induction t with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul x y => simp

theorem transl_mulP (n : ℕ) (a : G.A n) : G.transl n (G.mulP n a) = G.mulP n a ⊗ₜ 1 := by
  rw [transl_apply, ← pullTwo_comul]
  conv_rhs => rw [← (TensorProduct.rid R _).apply_symm_apply a, TensorProduct.rid_symm_apply,
    ← Coalgebra.lTensor_counit_comul]
  generalize comul (R := R) a = t
  induction t with
  | add x y hx hy => simp only [map_add (f := _), add_tmul, hx, hy]
  | tmul x y => simp [resOne_mulP, Algebra.algebraMap_eq_smul_one, smul_tmul]

theorem pullbackTwo_mulP_injective (n : ℕ) : Function.Injective (pullbackTwo (G.mulP n)) :=
  TensorProduct.map_injective_of_flat_flat _ _ (Test.mulP_injective G n) (Test.mulP_injective G n)

theorem res_eq_zero_of_cobOne_eq_zero (hp : (p : R) = 0) (n : ℕ) {b : G.A (n + 1)}
    (hb : cobOne R _ b = 0) : G.res n b = 0 :=
  Test.mulP_injective G n (by
    rw [mulP_res, (mulBy_of_cobOne_eq_zero hb p).1, ← Nat.cast_smul_eq_nsmul R, hp, zero_smul,
      map_zero])

theorem eq_zero_of_cob_eq_zero (hp : (p : R) = 0) {B : G.funs} (hB : G.cob B = 0) : B = 0 :=
  Subtype.ext (funext fun n => (B.2 n).symm.trans (G.res_eq_zero_of_cobOne_eq_zero hp n
    (congrArg (fun c : G.cocycles => c.1 (n + 1)) hB)))

theorem rigOfOmega_injective_of_eq_zero (hp : (p : R) = 0) : Function.Injective G.rigOfOmega := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).1 hw
  rw [G.eq_zero_of_cob_eq_zero hp (congrArg Prod.fst hb), map_zero] at hb
  exact (congrArg Prod.snd hb).symm

theorem omegaLevel_one_bijective (hp : (p : R) = 0) : Function.Bijective (G.omegaLevel 1) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun w hw => ?_, G.omegaLevel_surjective 1⟩
  obtain ⟨v, rfl⟩ := (G.omega_val_eq_zero_iff 1 w).1 hw
  rw [pow_one, hp, zero_smul]

def primLie : LinearMap.ker (cobOne R (G.A 1)) →ₗ[R] G.dual.Lie :=
  (G.dual.omegaLevel 1).dualMap ∘ₗ primTangent R (G.A 1)

theorem primLie_apply (b : LinearMap.ker (cobOne R (G.A 1))) (w : G.dual.omega)
    (φ : CartierDual R (G.A 1)) (h : w.1 1 = dUnit (R := R) φ) : G.primLie b w = φ b.1 :=
  (congrArg (primTangent R (G.A 1) b) h).trans (primTangent_d b φ)

end PDivGroup

end GlobalTheory

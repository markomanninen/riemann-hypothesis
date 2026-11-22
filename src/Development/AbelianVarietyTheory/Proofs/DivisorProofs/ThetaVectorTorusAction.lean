module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FsubMinorMinus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaWeightArithmeticAtPlaceProof
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftInfinityTypesAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilMaximalCompactFockSubstitutionCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeCoefficientWeightEqMinorWeightsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt

@[expose] public section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.MinorWeight

open GlobalTheory.JointHarm

theorem detPlus_diagonal {m : ℕ} (ε : Fin m → Bool) (d : Fin m → ℂ) :
    detP ε (diagonal d) = ∏ a, if ε a then d a else 1 := by
  have e : (1 / 2 : ℂ) • (1 + Formalism.REAL.Jm ε) * diagonal d + (1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε) =
      diagonal fun a => if ε a then d a else 1 := by
    ext a b
    by_cases h : a = b
    · subst h
      cases e : ε a <;> simp [Formalism.REAL.Jm, e] <;> ring
    · simp [Formalism.REAL.Jm, h]
  rw [detP, e, det_diagonal]

theorem detM_diagonal {m : ℕ} (ε : Fin m → Bool) (d : Fin m → ℂ) :
    detM ε (diagonal d) = ∏ a, if ε a then 1 else d a := by
  have e : (1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε) * diagonal d + (1 / 2 : ℂ) • (1 + Formalism.REAL.Jm ε) =
      diagonal fun a => if ε a then 1 else d a := by
    ext a b
    by_cases h : a = b
    · subst h
      cases e : ε a <;> simp [Formalism.REAL.Jm, e] <;> ring
    · simp [Formalism.REAL.Jm, h]
  rw [detM, e, det_diagonal]

theorem fact_diagonal {D : D7} {m n : ℕ} (ε : D.what₂.Tau → Fin m → Bool) (p q : D.what₂.Tau → ℕ)
    (ap am : D.what₂.Tau → ℕ → ℕ) (x₁ x₂ x₃ : D.what₂.Tau → ℤ) (hmn : m ≤ n) (hpq : ∀ τ, p τ + q τ = m)
    (hε : ∀ τ a, ε τ a = decide ((a : ℕ) < p τ)) (hap : ∀ τ a b, a ≤ b → b < p τ → ap τ b ≤ ap τ a)
    (ham : ∀ τ a b, a ≤ b → b < q τ → am τ b ≤ am τ a) (d : D.what₂.Tau → Fin m → ℂ) (hd : ∀ τ a, d τ a ≠ 0) :
    fact ε x₁ x₂ x₃ (fun τ => diagonal (d τ)) (fun _ => 1) (delta p q ap am : PolF D m n) =
      (∏ τ, ∏ a, d τ a ^ (if (a : ℕ) < p τ then (ap τ a : ℤ) + x₁ τ else -(am τ (a - p τ) : ℤ) + x₂ τ)) •
        (delta p q ap am : PolF D m n) := by
  have h := DeltaEig.fsub_delta D m n ε p q ap am hmn hpq hε hap ham (fun τ => diagonal (d τ)) (fun _ => 1)
    (fun τ => ⟨by
      rw [Matrix.isUnit_iff_isUnit_det, det_diagonal]
      exact (Finset.prod_ne_zero_iff.2 fun a _ => hd τ a).isUnit, by
      simp [Formalism.REAL.Jm, diagonal_mul_diagonal, mul_comm]⟩)
    (fun τ a b h => by
      obtain rfl : a = b := by
        by_contra e
        exact h (diagonal_apply_ne _ e)
      exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩)
    (fun τ => ⟨isUnit_one, fun a b h => Matrix.one_apply_ne h.ne⟩)
  rw [fact, LinearMap.smul_apply, AlgHom.toLinearMap_apply, h, smul_smul, fchar, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [detPlus_diagonal, detM_diagonal, det_one, _root_.one_zpow, mul_one, Matrix.one_apply_eq, Finset.prod_const_one,
    diagonal_apply_eq, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [hε]
  by_cases ha : (a : ℕ) < p τ <;> simp [ha, zpow_add₀ (hd τ a), mul_comm]

theorem pure_one {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (f : X → ℂ) : pureTensorL A f 1 = f := by
  have e : (1 : MvPolynomial ι ℂ) = MvPolynomial.basisMonomials ι ℂ 0 := by
    rw [MvPolynomial.coe_basisMonomials]; rfl
  rw [e]
  unfold pureTensorL
  rw [Module.Basis.constr_basis]
  simp [opPow]

theorem conj_mem {D : D7} {T : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel T S) (τ : D.what₂.Tau)
    {k : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hk : k ∈ Formalism.REAL.Kset (M.ε τ)) :
    (M.fr τ)⁻¹ * k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  have hk' : kᴴ * Formalism.REAL.Jm (M.ε τ) * k = Formalism.REAL.Jm (M.ε τ) := kset_uj hk
  have h3 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  show _ᴴ * _ * _ = _
  rw [← M.fr_gram τ]
  calc _ = (M.fr τ)ᴴ * (kᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * k) *
        M.fr τ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, h3, Matrix.mul_one, Matrix.mul_one, hk']

end GlobalTheory.AdTh.MinorWeight

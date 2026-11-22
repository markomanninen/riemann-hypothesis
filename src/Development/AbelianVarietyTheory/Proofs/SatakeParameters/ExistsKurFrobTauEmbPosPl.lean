module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SqrtInUnramifiedCompletion
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeOfLiesOver
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostFieldPadicEmbeddingMemMaxUnramified

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

open GlobalTheory.InertCompare GlobalTheory.Proof.IdempotentLatticeSequence

theorem exists_aut_of_algHoms {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [CharZero K]
    (f g : E →ₐ[ℚ] K) : ∃ u : E ≃ₐ[ℚ] E, ∀ x, g x = f (u x) := by
  have hmem : ∀ x, ∃ y, f y = g x := fun x => by
    have hs := Normal.splits (inferInstance : Normal ℚ E) x
    have hi : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    have hr : (((minpoly ℚ x).map (algebraMap ℚ E)).map (f : E →+* K)).IsRoot (g x) := by
      rw [Polynomial.map_map, AlgHom.comp_algebraMap_of_tower, Polynomial.IsRoot, Polynomial.eval_map_algebraMap,
        Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    exact hs.mem_range_of_isRoot (Polynomial.map_ne_zero (minpoly.ne_zero hi)) hr
  choose v hv using hmem
  have hf : Function.Injective f := f.toRingHom.injective
  let w : E →ₐ[ℚ] E :=
    { toFun := v
      map_one' := hf (by rw [hv, map_one, map_one])
      map_mul' := fun a b => hf (by rw [hv, map_mul, map_mul, hv, hv])
      map_zero' := hf (by rw [hv, map_zero, map_zero])
      map_add' := fun a b => hf (by rw [hv, map_add (f := _), map_add (f := _), hv, hv])
      commutes' := fun r => hf (by
        rw [hv, AlgHom.commutes, AlgHom.commutes]) }
  exact ⟨AlgEquiv.ofBijective w (AlgHom.normal_bijective ℚ E E w), fun x => (hv x).symm⟩

theorem exists_aut_of_embeddings {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [CharZero K]
    (f g : E →+* K) : ∃ u : E ≃ₐ[ℚ] E, ∀ x, g x = f (u x) :=
  exists_aut_of_algHoms f.toRatAlgHom g.toRatAlgHom

theorem padic_mem_Kur (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) : algebraMap ℚ_[p] ℂ_[p] x ∈ MaximalUnramifiedExtension p := by
  have hc : Continuous (algebraMap ℚ_[p] ℂ_[p]) := (algebraMap_isometry ℚ_[p] ℂ_[p]).continuous
  refine (Padic.denseRange_ratCast p).induction_on (p := fun x => algebraMap ℚ_[p] ℂ_[p] x ∈ MaximalUnramifiedExtension p) x ?_ ?_
  · exact Formalism.L2.Th1.D.GaussNormEstimates.isClosed_Kur.preimage hc
  · intro q
    simp

theorem coe_mem_Kur (p : ℕ) [Fact p.Prime] {x : PadicAlgCl p} (hx : x ∈ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension p) :
    algebraMap (PadicAlgCl p) ℂ_[p] x ∈ MaximalUnramifiedExtension p := by
  unfold Formalism.BasicNotions.Loc.MaximalUnramifiedExtension at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, hm, hpm, h1⟩ := hx
    exact Formalism.L2.Th1.D.GaussNormEstimates.mu_mem_Kur hm hpm (by rw [← map_pow, h1, map_one])
  | algebraMap x =>
    rw [← IsScalarTower.algebraMap_apply]
    exact padic_mem_Kur p x
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem host_image_mem_Kur_complex {R : Ranks} (H : Host R) (p : ℕ) [Fact p.Prime] (h2 : p ∉ H.small) (hq : p ≠ H.q)
    (hd : p ≠ H.d) (ρ : H.E →+* ℂ_[p]) (x : H.E) : ρ x ∈ MaximalUnramifiedExtension p := by
  have : IsGalois ℚ H.E := H.hostE_isGalois
  let c : H.E →+* PadicAlgCl p := (IsAlgClosed.lift : H.E →ₐ[ℚ] PadicAlgCl p)
  obtain ⟨u, hu⟩ := exists_aut_of_embeddings ((algebraMap (PadicAlgCl p) ℂ_[p]).comp c) ρ
  rw [hu, RingHom.comp_apply]
  exact coe_mem_Kur p (GlobalTheory.HostKur.host_image_mem_Kur H p h2 hq hd c _)

theorem exists_kur_frob_tauEmb_posPl : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (z : Bool × HH D) (y : D.host.E), ∃ a : MaximalUnramifiedExtension p, (a : ℂ_[p]) = tauEmb D lam (tauPl D z) y ∧ ((σ a : MaximalUnramifiedExtension p) : ℂ_[p]) = tauEmb D lam (tauPl D (posPl D p z 1)) (D.host.conj y) := by
  intro D p _ lam σ hσ h z y
  have ⟨h2, hq, hd⟩ : p ∉ D.host.small ∧ p ≠ D.host.q ∧ p ≠ D.host.d := by
    rcases h with h | h
    · have k := (primeClass_eq_inert_iff D.host.toHostRaw).1 h
      exact ⟨k.1, k.2.1, k.2.2.1⟩
    · have k := (primeClass_eq_signal_iff D.host.toHostRaw).1 h
      exact ⟨k.1, k.2.1, k.2.2.1⟩
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = rhoH D lam (tauPl D z) := ⟨_, rfl⟩
  have hK : ∀ x, ρ x ∈ MaximalUnramifiedExtension p := host_image_mem_Kur_complex D.host p h2 hq hd ρ
  let ρ' : D.host.E →+* MaximalUnramifiedExtension p := ρ.codRestrict (MaximalUnramifiedExtension p) hK
  have hρ' : ∀ x, ((ρ' x : MaximalUnramifiedExtension p) : ℂ_[p]) = ρ x := fun _ => rfl
  let ρ2 : D.host.E →+* ℂ_[p] := (MaximalUnramifiedExtension p).subtype.comp (σ.comp ρ')
  obtain ⟨g, hg⟩ := exists_aut_of_embeddings ρ ρ2
  have := primeOf_isPrime ρ
  have hL := primeOf_liesOver ρ
  have hc : Nat.card (ℤ ⧸ Ideal.under ℤ (primeOf ρ)) = p := by
    rw [← hL.over, Int.card_ideal_quot]
  have hgF : IsArithFrobAt ℤ g (primeOf ρ) := by
    intro x
    rw [hc, mem_primeOf]
    have hx : ‖ρ' (x : D.host.E)‖ ≤ 1 := norm_int_le ρ x
    have h3 := hσ.2.2.2.2 _ hx
    have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    refine lt_of_le_of_lt ?_ hp1
    refine le_of_eq_of_le ?_ h3
    have e1 : ρ (algebraMap (𝓞 D.host.E) D.host.E ((MulSemiringAction.toAlgHom ℤ (𝓞 D.host.E) g) x - x ^ p)) =
        ((σ (ρ' (x : D.host.E)) - ρ' (x : D.host.E) ^ p : MaximalUnramifiedExtension p) : ℂ_[p]) := by
      have e0 : algebraMap (𝓞 D.host.E) D.host.E ((MulSemiringAction.toAlgHom ℤ (𝓞 D.host.E) g) x) = g (x : D.host.E) := rfl
      rw [map_sub, map_sub, e0, ← hg, map_pow, map_pow]
      rfl
    rw [e1]
    rfl
  obtain ⟨φ, hφ⟩ := (D.host.der.frob p (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd) (primeOf ρ)).1
  have hgφ : g = φ := by
    have hI := hgF.mul_inv_mem_inertia hφ
    have h1 := ((D.host.der.frob p (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd) (primeOf ρ)).2.2.2 (g * φ⁻¹)).1 (fun x => hI x)
    exact mul_inv_eq_one.1 h1
  have hcc : D.host.conj (D.host.conj y) = y := D.host.φ₀.injective (by
    rw [D.host.conjE_apply, D.host.conjE_apply, Complex.conj_conj])
  refine ⟨ρ' y, ?_, ?_⟩
  · rw [hρ', hρ, ← coe_rhoH]
  · have hplGG : ∀ z : Bool × HH D, plGG D (posPl D p z 1) = plGG D z * D.host.galE φ * D.R.cc := by
      have hC := factClassFrob D.R D.host p (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd) (primeOf ρ) φ hφ
      have hc := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd)
      have hne : ∃ g, g ∈ Formalism.MainNotions.G.frobSet D p := ⟨_, primeOf ρ, inferInstance, inferInstance, φ, hφ, rfl⟩
      obtain ⟨P₀, hP₀, hL₀, σ₀, hσ₀, hg₀⟩ := Classical.epsilon_spec hne
      have e1 := (D.host.toHostAx.frob_iff p hc (primeOf ρ) φ).1 hφ
      have e2 := (@Formalism.HC.HostAx.frob_iff _ D.host.toHostAx p _ hc P₀ hP₀ hL₀ σ₀).1 hσ₀
      have hH : (D.host.galE φ).2 = D.R.iota (G.hP D p) := by
        unfold Formalism.MainNotions.G.hP
        rw [Formalism.HC.Frame.iota_iotaInv, ← hg₀]
        exact congrArg Prod.snd (e1.trans e2.symm)
      have hp : ∀ z : Bool × HH D, plGG D z = ((if z.1 then -1 else 1, 1), D.R.iota z.2) := by
        rintro ⟨b, t⟩
        cases b <;> rfl
      intro z
      rw [hp, hp]
      refine Prod.ext ?_ ?_
      · rcases h with h | h
        · have h1 := hC.2.2.1 h
          have hs : ¬ IsSg D p := fun hs => by have := h.symm.trans hs; cases this
          simp only [Prod.fst_mul, h1, Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0, posPl, partner, hs]
          cases z.1 <;> simp
        · have h1 := hC.2.1.1 h
          have hp : (partner D p z.2 1).1 = true := decide_eq_true ⟨h, odd_one⟩
          simp only [Prod.fst_mul, h1, Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0, posPl, hp]
          cases z.1 <;> simp
      · simp only [Prod.snd_mul, Formalism.HC.Frame.cc, mul_one, hH, posPl, partner, one_smul]
        rw [Formalism.HC.Frame.iota_add]
    have hemb : ∀ (g : _ ) (σ : D.host.E ≃ₐ[ℚ] D.host.E) (x : D.host.E), D.host.emb (g * D.host.galE σ) x = D.host.emb g (σ x) := by
      intro g σ x
      have he : D.host.sigmaOf (g * D.host.galE σ) = D.host.sigmaOf g * σ := by
        unfold Host.sigmaOf
        rw [map_mul, MulEquiv.symm_apply_apply]
      change D.host.φ₀ (D.host.sigmaOf (g * D.host.galE σ) x) = D.host.φ₀ ((D.host.sigmaOf g * σ) x)
      rw [he]
    have het : ∀ z : Bool × HH D, embT D (tauPl D z) = D.host.emb (plGG D z) := by
      intro z
      unfold embT tauPl
      rw [Equiv.apply_symm_apply]
    have h4 : rhoH D lam (tauPl D (posPl D p z 1)) (D.host.conj y) = rhoH D lam (tauPl D z) (φ (D.host.conj (D.host.conj y))) := by
      rw [rhoH_apply, rhoH_apply, het, het, hplGG, ← D.host.galE_conjE, hemb, hemb]
    rw [hcc] at h4
    rw [← coe_rhoH, h4, ← hρ, ← hgφ, ← hg]
    rfl

end GlobalTheory.KerStd

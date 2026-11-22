module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjStabilizersSelfDualLatticesUnramified
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero

import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBoundLatLoc

@[expose] public section

open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem fullLattice_of_isSelfDualAt
    {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : IsHermND σ J) {L : Submodule (𝓞 E) (Fin n → E)} (hLat : Submodule.IsLattice E L)
    {v : HeightOneSpectrum (𝓞 F)} (hL : IsSelfDualAt σ J L v) : Submodule.IsFullLattice E L := by
  classical
  refine { toIsLattice := hLat, span_eq_top := ?_ }
  by_contra hspan
  obtain ⟨f, hf, hker⟩ := (Submodule.span E (L : Set (Fin n → E))).exists_le_ker_of_lt_top
    (lt_top_iff_ne_top.mpr hspan)
  let coeff (i : Fin n) : E := f (fun j => if i = j then 1 else 0)
  have hcoeff (x : Fin n → E) : f x = ∑ i, x i * coeff i := f.pi_apply_eq_sum_univ x
  let w := J⁻¹ *ᵥ fun i => σ (coeff i)
  have hw : J *ᵥ w = fun i => σ (coeff i) := by
    dsimp only [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hJ.2.isUnit, Matrix.one_mulVec]
  have hw_ne : w ≠ 0 := by
    intro hw_zero
    have hc (i : Fin n) : coeff i = 0 := σ.injective (by
      simpa [hw_zero] using (congrFun hw i).symm)
    apply hf
    exact LinearMap.ext fun x => by simp [hcoeff, hc]
  have hOrth (x : Fin n → E) (hx : x ∈ L) : hE σ J x w = 0 := by
    have hfx : f x = 0 := LinearMap.mem_ker.mp (hker (Submodule.subset_span hx))
    unfold hE Formalism.UG.hform
    simp only [mul_assoc, ← Finset.mul_sum]
    change (∑ i, σ (x i) * (J *ᵥ w) i) = 0
    rw [hw]
    calc
      _ = σ (f x) := by rw [hcoeff, map_sum]; simp only [map_mul]
      _ = 0 := by rw [hfx, map_zero]
  let wLoc : Fin n → Fv F v ⊗[F] E := fun i => (1 : Fv F v) ⊗ₜ[F] w i
  let pairing : (Fin n → Fv F v ⊗[F] E) →+ (Fv F v ⊗[F] E) :=
    { toFun := fun x => hLin σ J (Fv F v) wLoc x
      map_zero' := by simp [hLin, hR, Formalism.UG.hform]
      map_add' := fun x y => by
        simp [hLin, hR, Formalism.UG.hform, add_mul, Finset.sum_add_distrib] }
  have hZero : ∀ x ∈ latLoc F L v, pairing x = 0 := by
    intro z hz
    refine latLoc_induction (p := fun x => pairing x = 0) (fun a _ x hx => ?_) (map_zero pairing)
      (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
      (fun x hx => by rw [map_neg, hx, neg_zero]) hz
    change hLin σ J (Fv F v) wLoc (fun i => a ⊗ₜ[F] x i) = 0
    have h := congrArg (fun z : E => a ⊗ₜ[F] z) (hOrth x hx)
    simpa [hLin, hR, hE, Formalism.UG.hform, wLoc, sigR, JR, inclR,
      TensorProduct.tmul_sum, Algebra.TensorProduct.tmul_mul_tmul] using h
  have hLine (a : Fv F v) : (fun i => a ⊗ₜ[F] w i) ∈ latLoc F L v := by
    rw [show latLoc F L v = dualLoc σ J L v from hL]
    change ∀ x ∈ latLoc F L v, hLin σ J (Fv F v) (fun i => a ⊗ₜ[F] w i) x ∈ intLoc F E v
    intro x hx
    have he : (fun i => a ⊗ₜ[F] w i) = (a ⊗ₜ[F] (1 : E)) • wLoc := by
      funext i
      change _ = (a ⊗ₜ[F] (1 : E)) * ((1 : Fv F v) ⊗ₜ[F] w i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [he, hLin_smul_left, show hLin σ J (Fv F v) wLoc x = 0 from hZero x hx, mul_zero]
    exact zero_mem _
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw_ne
  change w i ≠ 0 at hi
  obtain ⟨C, hC⟩ := GlobalTheory.LocalLatticeBound.exists_bound_latLoc L v
  let τ : E →ₐ[F] FvBar F v := IsAlgClosed.lift
  have hpos : 0 < absBar F v (τ (w i)) :=
    pos_iff_ne_zero.mpr fun h => hi (τ.injective (by simpa using (absBar_eq_zero F v).mp h))
  let _ : NontriviallyNormedField (Fv F v) :=
    Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  obtain ⟨a, ha⟩ := NormedField.exists_lt_nnNorm (Fv F v) (C / absBar F v (τ (w i)))
  have hbound := (le_absFin F v τ (a ⊗ₜ[F] w i)).trans (hC _ (hLine a) i)
  rw [finEmb_tmul, absBar_mul, absBar_algebraMap] at hbound
  exact (not_lt_of_ge hbound) ((div_lt_iff₀ hpos).mp ha)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_stabilizers_selfDual_lattices_unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (L L' : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → Submodule.IsLattice E L' → ∀ v : HeightOneSpectrum (𝓞 F), IsSelfDualAt σ J L v → IsSelfDualAt σ J L' v → ∃ g : GLoc σ J v, ∀ k : GLoc σ J v, k ∈ stabLoc σ J L' v ↔ g⁻¹ * k * g ∈ stabLoc σ J L v := by
  intro F E _ _ _ _ _ σ hCM hU n J hJ L L' hLat hLat' v hL hL'
  exact GlobalTheory.SelfDualStabConj.exists_conj_stabLoc F E σ hCM hU n J hJ L L'
    (fullLattice_of_isSelfDualAt hJ hLat hL)
    (fullLattice_of_isSelfDualAt hJ hLat' hL') v hL hL'

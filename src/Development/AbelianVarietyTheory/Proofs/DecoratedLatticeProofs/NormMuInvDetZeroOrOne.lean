module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantFirst

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.ScalarModulusS

theorem norm_muInvDet_zero_or_one : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i < N.R.m → ∀ (n : ℕ) (L : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)) (σ : X.K →+* ℂ), ‖σ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) L fr)‖ = 0 ∨ ‖σ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) L fr)‖ = 1 := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ h i hi n L fr σ
  obtain ⟨hH, -, ⟨-, hσ, -, ⟨eta, ht⟩, -, hsel⟩, -, hmu, -, hI, -, -⟩ := h
  obtain ⟨-, -, -, -, -, -, hX, -, -, hPr, -⟩ := hH
  rw [← hσ] at ht
  have hS : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs := by
    intro P
    classical
    subst hmu
    rcases Finset.mem_union.1 P.2 with h | h
    · exact h
    · have h0 := twistPrimes_trivialTuple_empty sel Sg
      exact absurd (h0 ▸ h) (Finset.notMem_empty _)
  have hnorm : ‖σ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) L fr)‖ = 1 := by
    have hU := fun P x y hy => GlobalTheory.ScalarModulus.norm_eq_one_of_locK hX.ok hPr
      (ht.mu0 ⟨i, hi⟩) P x y hy σ
    have hval : ∀ P : HeightOneSpectrum (𝓞 X.E), (∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.asIdeal) →
        ‖σ (Ch.muVal ⟨i, hi⟩ P : X.K)‖ = 1 := fun P hP =>
      hU P (Formalism.L2.Host.unif P) _ (ht.muVal _ P hP)
    have hfin := GlobalTheory.CharVal.finOrder_tup mu
    have hmuq : ∀ P : rowSG Pr sel mu, ‖σ (cst.muq (i + 1) P)‖ = 1 := by
      intro P
      have hq : ‖σ ((qValC (mu : Chr X.F X.E X.K) P.1 : X.Kˣ) : X.K)‖ = 1 :=
        GlobalTheory.GO.norm_map_of_finOrder _ (GlobalTheory.CharVal.finOrder_qVal hfin P.1)
      have hqG := hI.muqG i hi P (hS P) (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) rfl
      have hloc : G.σ₀ ((cst.muq (i + 1) P * ((qValC (mu : Chr X.F X.E X.K) P.1 : X.Kˣ) : X.K))⁻¹) =
          (((G.mu0 ⟨i, hi⟩).locK P.1 (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) : ℂˣ) : ℂ) := by
        rw [map_inv₀, map_mul, hqG, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one, inv_inv]
      have hnormLoc := hU P.1 _ _ hloc
      rwa [map_inv₀, map_mul, norm_inv, norm_mul, hq, mul_one, inv_eq_one] at hnormLoc
    have hoff : ‖σ (muOff sel (rowSG Pr sel mu) (mUof Ch mu i) L)‖ = 1 := by
      unfold muOff
      refine finprod_induction (fun x => ‖σ x‖ = 1) (by simp)
        (fun x y hx hy => by rw [map_mul, norm_mul, hx, hy, one_mul]) fun v => ?_
      split_ifs with hv
      · simp
      · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, norm_zpow, mUof, dite_eq_left hi, Units.val_mul,
          Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀, norm_mul,
          norm_inv, norm_inv, hval _ (GlobalTheory.ColPeriod.Scal.g_notMem_sel hX.ok hPr hsel hv),
          GlobalTheory.GO.norm_map_of_finOrder _ (GlobalTheory.CharVal.finOrder_unifVal hfin _)]
        simp
    rw [muInvDet, map_mul, norm_mul, hoff, one_mul, map_prod, norm_prod]
    refine Finset.prod_eq_one fun P _ => ?_
    unfold muAt
    obtain ⟨z, ζ, hζ, e⟩ := GlobalTheory.LocCharVal.locChar_eq_zpow_mul X.E X.K P.1 (qOf P.1) (cst.muq (i + 1) P) _
      ((LinearEquiv.det (fr P) : X.Eˣ) : X.E)
      (GlobalTheory.CharVal.val_natCast_of_notMem_sq (Ideal.absNorm_mem _)
        (GlobalTheory.ColPeriod.levelPrimes X Pr sel Sg mu hX.ok hPr hsel P).1.2) (Units.ne_zero _)
    rw [e, map_mul, map_zpow₀, norm_mul, norm_zpow, hmuq, GlobalTheory.GO.norm_map_of_finOrder _ hζ,
      one_zpow, one_mul]
  exact Or.inr hnorm

end GlobalTheory.ScalarModulusS

module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingDoubleCosetVolumeBound
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
open ValuativeRel Matrix MeasureTheory GroundTheory.Automorphic.GLnLocal
open GlobalTheory.CompanionTheory.ContractVolume

private theorem leviEmbZjDiagonal {k : Type} [Field k] {h N : ℕ}
    (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) :
    leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) =
      diagT k (Fin N) (fun i => if Zl.JC.blockIdx d hd i ≤ j then t else 1) := by
  apply Units.ext
  rw [val_diagT]
  ext i l
  obtain ⟨⟨a, x⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := (stdBlocks d hd).surjective l
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hxy : x = y
    · subst hxy
      by_cases ha : a ≤ j <;> simp [Zl.JC.zj, Zl.JC.blockIdx, ha, Matrix.GeneralLinearGroup.scalar]
    · have hne : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨a, y⟩ := fun e => hxy (by
        have := (stdBlocks d hd).injective e
        simpa using this)
      rw [Matrix.diagonal_apply_ne _ hne]
      by_cases ha : a ≤ j <;> simp [Zl.JC.zj, ha, Matrix.GeneralLinearGroup.scalar, hxy]
  · have hne : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨b, y⟩ := fun e => hab (by
      have := (stdBlocks d hd).injective e
      exact congrArg Sigma.fst this)
    rw [Matrix.diagonal_apply_ne _ hne, leviEmb_apply_ne k _ _ hab]

theorem _root_.GlobalTheory.T.contracting_double_coset_volume_bound :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) →
        ∀ (t : kˣ), valuation k (t : k) < 1 → ∀ (j : Fin h), j.val + 1 < h →
          ∀ (m : ℕ), 1 ≤ m → ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)]
            (μ : Measure (AdGL k N)), μ.IsHaarMeasure →
              ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ,
                ENNReal.ofReal (c * (modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j))⁻¹ ^ r) ≤
                  μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
                    {g | ∃ x ∈ congruenceSubgroup k N m, ∃ y ∈ congruenceSubgroup k N m,
                      g = x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y}) := by
  intro k _ _ _ _ h N d hd _ t ht j _ m hm _ _ μ hμ
  have := hμ
  obtain ⟨n, p, u, hp, hu, htu⟩ := exists_decomp t ht
  have hK := coe_congruenceSubgroup k N m hm
  rw [← hp] at hK
  have hϖ1 : valuation k (p : k) < 1 := hp ▸ valuation_uniformizer_lt_one k
  have hunif : ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k (p : k) := fun x hx =>
    hp ▸ le_valuation_uniformizer k x hx
  obtain ⟨hpos, hfin⟩ := GlobalTheory.CompanionTheory.PrincipalCongruence.measure_image_principal_pos_lt_top k N (p : k) m
    p.ne_zero hϖ1 hunif hm μ hμ
  rw [← hK] at hpos hfin
  let a : Fin N → ℤ := fun i => if Zl.JC.blockIdx d hd i ≤ j then (n : ℤ) else 0
  have ha : Antitone a := by
    intro x y hxy
    have hmono := GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone h N d hd hxy
    show (if _ then _ else _) ≤ (if _ then _ else _)
    by_cases hy : Zl.JC.blockIdx d hd y ≤ j
    · simp [hy, hmono.trans hy]
    · simp [hy]
      split_ifs <;> simp
  let D : GL (Fin N) k := diagT k (Fin N) (fun i => p ^ a i)
  have hD : (D : Matrix (Fin N) (Fin N) k) = Matrix.diagonal (fun i => (p : k) ^ a i) := by
    simp [D, val_diagT]
  let w : GL (Fin N) k := diagT k (Fin N) (fun i => if Zl.JC.blockIdx d hd i ≤ j then u else 1)
  have hw : w ∈ integralGL k N := by
    refine diagT_mem_integralGL _ fun i => ?_
    split_ifs
    · exact hu
    · simp
  have hfac : leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) = D * w := by
    rw [leviEmbZjDiagonal, ← map_mul]
    congr 1
    funext i
    by_cases hi : Zl.JC.blockIdx d hd i ≤ j
    · simp [a, hi, htu]
    · simp [a, hi]
  have hcomm : Commute D w := by
    show D * w = w * D
    rw [← map_mul, ← map_mul, mul_comm]
  have hmod : (modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j))⁻¹ =
      (resCard k : ℝ) ^ (n * ((∑ a, if a ≤ j then d a else 0) * ∑ b, if j < b then d b else 0)) := by
    have h1 : nabs k t = ((resCard k : ℝ)⁻¹) ^ n := by
      have h2 := nabs_uniformiser (irreducible_uniformizer k) hp
      have h3 := nabs_eq_one_of_valuation_eq_one hu
      rw [htu, show nabs k (p ^ n * u) = nabs k (p ^ n) * nabs k u from nabs_mul k _ _, nabs_pow', h2, h3,
        mul_one]
    have h4 : (∑ a, if a ≤ j then (d a : ℤ) else 0) * (∑ b, if j < b then (d b : ℤ) else 0) =
        (((∑ a, if a ≤ j then d a else 0) * ∑ b, if j < b then d b else 0 : ℕ) : ℤ) := by
      push_cast
      rfl
    rw [modulus_zj, sum_modExp, h4, h1, zpow_natCast, ← pow_mul, inv_pow, inv_inv]
  refine ⟨(μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
    (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m : Set (GL (Fin N) k)))).toReal,
    ENNReal.toReal_pos hpos.ne' hfin.ne, fun r => ?_⟩
  have hvol := GlobalTheory.CompanionTheory.DoubleCosetVolume.measure_image_doubleCoset k N (p : k) m a p.ne_zero hϖ1 hunif
    hm ha D hD μ hμ r
  rw [← hK, sum_toNat d hd j n] at hvol
  have hle := measure_le_translate μ (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m) (D ^ r) (w ^ r)
    (hcomm.pow_pow r r) (fun x hx => conj_mem_congruenceSubgroup k N ((integralGL k N).pow_mem hw r) hx)
  rw [hfac, hcomm.mul_pow, hmod]
  refine le_trans (le_of_eq ?_) hle
  simp only [SetLike.mem_coe] at hvol
  rw [hvol, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin.ne, mul_comm,
    ← pow_mul, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast, mul_comm _ r]
  rfl

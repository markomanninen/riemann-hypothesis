module

public import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
public import Development.AutomorphicArithmetic.PrimitiveCosets.LevelFamily
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow

@[expose] public section

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

theorem UpperTheory.Comparison₂.formB :
    ∀ Λ : Level, Λ.FormB := by
  intro Λ la hla θ hθ0 hθ1 hW
  classical
  let weight (ψ : PChar) : ℝ := if ψ = PChar.one then 1 else Λ.wt ψ
  have weight_pos (ψ : PChar) : 0 < weight ψ := by
    unfold weight Level.wt
    split_ifs
    · exact one_pos
    · exact one_pos
    · positivity
  have admissible (ψ : PChar) : ψ.N = 1 ∨ ψ.χ ≠ 1 := by
    by_cases h : ψ.χ = 1
    · left
      have hp := ψ.prim
      rw [DirichletCharacter.IsPrimitive, h, DirichletCharacter.conductor_one] at hp
      exact hp.symm
    · exact Or.inr h
  let F : Deduction.CharFamily :=
    @Deduction.CharFamily.mk Λ.KEPT _ (fun i => i.1.N) (fun i => i.1.ne)
      (fun i => i.1.χ) (fun i => weight i.1) (fun i => weight_pos i.1)
      (fun i => admissible i.1)
  have hG (y : ℝ) : Deduction.Gm F y = Λ.Gm y := by
    change (∑ i : Λ.KEPT, weight i.1 * (Deduction.Gchi i.1.χ y).re) = Λ.Gm y
    rw [Finset.sum_coe_sort Λ.KEPT (fun ψ => weight ψ * (Deduction.Gchi ψ.χ y).re),
      ← Finset.add_sum_erase _ _ Λ.one_mem, Level.Gm, Level.Nt]
    congr 1
    · have hGz : Formalism.Gz y = An.G y := by
        unfold Formalism.Gz Formalism.Sz An.G
        have hsum : (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / n - 1)) =
            ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / n - 1) 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          obtain ⟨hn₁, hn₂⟩ := Finset.mem_Icc.mp hn
          have hn_pos : 0 < n := Nat.zero_lt_of_lt hn₁
          have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff' hn_pos.ne').mp hn₂
          have hnonneg : 0 ≤ y / (n : ℝ) - 1 := by
            rw [sub_nonneg, le_div_iff₀ (Nat.cast_pos.mpr hn_pos), one_mul]
            exact hny
          rw [max_eq_left hnonneg]
        rw [hsum]
        ring
      rw [show weight PChar.one = 1 by simp [weight], one_mul, ← gChi_eq, hGz]
      simp only [An.gChi, PChar.one]
      exact (congrArg Complex.re (ite_eq_left rfl)).trans (Complex.ofReal_re _)
    · refine Finset.sum_congr rfl fun ψ hψ => ?_
      have hne : ψ ≠ PChar.one := Finset.ne_of_mem_erase hψ
      simp only [weight, ite_eq_right hne, gChi_eq]
  have hZ (h : Deduction.ZeroFree F θ) : Λ.ZeroFreeAbove θ := by
    intro ψ hψ s hs
    exact h ⟨ψ, hψ⟩ s hs
  apply hZ
  refine Deduction.zeroFree_of_rpow_window F (δ := la - 1) (C := 1) hθ0 hθ1 (by linarith) fun Y₀ => ?_
  obtain ⟨Y, hY, hx⟩ := hW Y₀
  refine ⟨Y, hY, fun y hy => ?_⟩
  have h1 : (1 : ℝ) + (la - 1) = la := by ring
  rw [h1] at hy
  rw [hG, one_mul]
  exact hx y hy.1 hy.2

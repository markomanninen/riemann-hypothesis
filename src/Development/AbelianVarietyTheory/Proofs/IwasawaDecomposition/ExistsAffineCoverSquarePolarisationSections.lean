module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinCombPowSectionUnflattenStatement

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.SquarePolCover.exists_cover : AmpleSt → ∀ (R : Type) [CommRing R] [IsNoetherianRing R]
    (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 2 ≤ n → ∃ (κ : Type)
    (s : κ → H0 (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) n),
    (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
  intro hA R _ _ P n hn
  obtain ⟨κ, t, ht, hta⟩ := GlobalTheory.Algebraise.exists_cover hA P (2 * n) (by omega)
  have hm : ((2 * n : ℕ) : ℤ) = 2 * (n : ℤ) := by push_cast; ring
  have unflat : ∀ {X Y : Scheme.{0}} (L : LB X) (a n m : ℤ), m = a * n → ∀ (g : Y ⟶ X) (s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m))), ∃ s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g) (fun _ => n)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j → gs r z _ (s'.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j) := by
    intro X Y L a n m hm g s'
    have le : ∀ J : Fin 1 → (Fin 1 → L.ι),
        LB.wchart (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (fun _ : Fin 1 => g) J ≤
          LB.wchart L (fun _ : Fin 1 => g) (fun k => J k 0) := fun J y hy =>
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 hy k) 0
    refine ⟨⟨fun J => (Y.presheaf.map (homOfLE (le J)).op).hom (s'.f (fun k => J k 0)), fun J J' => ?_⟩, ?_⟩
    · refine fn_ext fun y hy => ?_
      have hy1 : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J k 0) := le J hy.1
      have hy2 : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J' k 0) := le J' hy.2
      have hS : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J k 0) ⊓
          (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J' k 0) := ⟨hy1, hy2⟩
      have c := congrArg (gs (𝟙 Y) y _) (s'.compat (fun k => J k 0) (fun k => J' k 0))
      rw [gs_res (𝟙 Y) y _ hS, gs_mul (𝟙 Y) y _ hS, gs_unit (𝟙 Y) y _ hS, gs_res (𝟙 Y) y _ hS] at c
      erw [gm_linComb L _ _ (𝟙 Y) y _ _ hy1 hy2] at c
      erw [gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy.1, gs_mul (𝟙 Y) y _ hy, gs_unit (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy,
        gs_res (𝟙 Y) y _ hy.2, c]
      erw [gm_linComb _ _ _ (𝟙 Y) y J J' hy.1 hy.2]
      have i1 : (𝟙 Y ≫ g) y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)).U (J 0) := by
        simpa using Set.mem_iInter.1 hy.1 0
      have i2 : (𝟙 Y ≫ g) y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)).U (J' 0) := by
        simpa using Set.mem_iInter.1 hy.2 0
      simp only [Fin.prod_univ_one]
      erw [gm_linComb L _ _ (𝟙 Y ≫ g) y (J 0) (J' 0) i1 i2]
      simp only [Fin.prod_univ_one, Category.comp_id, Category.id_comp, hm, zpow_mul]
      rfl
    · intro Z r z j h
      exact (gs_res r z (le _) (Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => h) _).symm
  choose s hs using fun i => unflat P.L 2 n ((2 * n : ℕ) : ℤ) hm (𝟙 P.A.left) (t i)
  have key : ∀ i, nonzeroLocus (s i) = nonzeroLocus (t i) := by
    intro i
    ext x
    obtain ⟨j, hj⟩ := exists_chart P.isLB x
    have h₁ := GlobalTheory.SectionRingIso.mem_iff_isUnit (t i) (𝟙 _) x (j := fun _ => j) hj
    have h₂ := GlobalTheory.SectionRingIso.mem_iff_isUnit (s i) (𝟙 _) x (j := fun _ => fun _ => j)
      (GlobalTheory.SectionRingIso.mem_ch.2 hj)
    have h₃ := hs i P.A.left (𝟙 _) x j hj
    exact h₂.trans ((congrArg IsUnit h₃).to_iff.symm.trans h₁.symm)
  refine ⟨κ, s, ?_, fun i => ?_⟩
  · simp_rw [key]; exact ht
  · rw [key]; exact hta i

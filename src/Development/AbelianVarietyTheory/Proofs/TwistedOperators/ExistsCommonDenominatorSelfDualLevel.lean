module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNsmulMemOfSpan

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelDenom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem natCast_smul_mem_hatL_std (Λ : Submodule (𝓞 E) (Fin n → E)) (c : ℕ)
    (hc : ∀ y ∈ Λ, c • y ∈ Formalism.L2.Col.stdLat E n) (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hx : x ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    (c : E ⊗[F] Formalism.L2.Herm.Af F) • x ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (Formalism.L2.Col.stdLat E n) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨c • l, hc l hl, ?_⟩
    funext i
    simp [nsmul_eq_mul, map_mul, map_natCast]
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul a y _ hy =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hy

theorem exists_nsmul_le_std (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG) :
    ∃ c : ℕ, 0 < c ∧ ∀ y ∈ Λ, c • y ∈ Formalism.L2.Col.stdLat E n := by
  obtain ⟨S, hS⟩ := hfg
  obtain ⟨c, hc, h⟩ := GlobalTheory.LatSandwich.exists_nsmul_le S (Formalism.L2.Pj.stdLat E n)
    (fun x _ => GlobalTheory.LatSandwich.exists_nsmul_mem_stdLat x)
  exact ⟨c, hc, fun y hy => h y (by rw [hS]; exact hy)⟩

theorem exists_nsmul_single_mem (Λ : Submodule (𝓞 E) (Fin n → E)) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ c : ℕ, 0 < c ∧ ∀ j, c • (Pi.single j (1 : E) : Fin n → E) ∈ Λ := by
  classical
  obtain ⟨c, hc, h⟩ := GlobalTheory.LatSandwich.exists_nsmul_le (Finset.univ.image fun j : Fin n => (Pi.single j (1 : E) : Fin n → E)) Λ
    (fun x _ => GlobalTheory.LatSandwich.exists_nsmul_mem_of_span Λ hsp x)
  exact ⟨c, hc, fun j => h _ (Submodule.subset_span (by simp))⟩

end GlobalTheory.LevelDenom

namespace GlobalTheory.LevelDenom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem exists_denom_stab (hc : Formalism.BasicNotions.CMData F E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ b : ℕ, 0 < b ∧ ∀ k ∈ congLev hc J Λ ⊤, ∀ i j,
      (b : E ⊗[F] Formalism.L2.Herm.Af F) * k.1 i j ∈ Formalism.L2.Herm.intAf F E := by
  classical
  obtain ⟨a, ha, hae⟩ := exists_nsmul_single_mem Λ hsp
  obtain ⟨c, hc0, hce⟩ := exists_nsmul_le_std Λ hfg
  refine ⟨a * c, Nat.mul_pos ha hc0, fun k hk i j => ?_⟩
  have hs := hk.2.1
  have hzmem : (fun l => Formalism.UG.inclE (Formalism.L2.Herm.Af F) ((a • (Pi.single j (1 : E) : Fin n → E)) l)) ∈
      Formalism.L2.Herm.hatL (F := F) Λ := Submodule.subset_span ⟨_, hae j, rfl⟩
  have ez : (fun l => Formalism.UG.inclE (Formalism.L2.Herm.Af F) ((a • (Pi.single j (1 : E) : Fin n → E)) l)) =
      (a : E ⊗[F] Formalism.L2.Herm.Af F) • (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) := by
    funext l
    by_cases e : l = j
    · subst e; simp [nsmul_eq_mul]
    · simp [Pi.single_eq_of_ne e, nsmul_eq_mul]
  rw [ez] at hzmem
  have hkz := (hs _).1 hzmem
  have h2 := natCast_smul_mem_hatL_std Λ c hce _ hkz
  rw [Formalism.L2.Col.mem_latS_std] at h2
  have h3 := h2 i
  rw [Matrix.mulVec_smul] at h3
  convert h3 using 1
  simp [Matrix.mulVec_single_one, mul_comm, mul_left_comm, mul_assoc]

end GlobalTheory.LevelDenom

namespace GlobalTheory.LevelDenom

theorem exists_denom_congLev : ∀ (D : D7) (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ → ∃ b : ℕ, 0 < b ∧ ∀ k ∈ congLev D.sp.cm V.gram Λ ⊤, ∀ i j, (b : Lev.EAf D) * k.1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D V Λ hΛ
  classical
  haveI := hΛ.1
  obtain ⟨c, hc, hcΛ⟩ := exists_nsmul_le_std Λ (Submodule.IsLattice.fg D.host.E Λ)
  have hsp : Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) = ⊤ := by
    apply top_unique
    intro y _
    let t : Fin V.rank → D.host.E := fun i => ∑ j, V.gram i j * y j
    obtain ⟨d, hd, hdt⟩ := GlobalTheory.LatSandwich.exists_nsmul_mem_stdLat t
    have hy : (c * d) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hcx := (GlobalTheory.LatSandwich.mem_stdLat_iff _).1 (hcΛ x hx)
      have hdt' := (GlobalTheory.LatSandwich.mem_stdLat_iff _).1 hdt
      have hint : IsIntegral ℤ (∑ i, star ((c • x) i) * (d • t) i) := by
        apply IsIntegral.sum
        intro i _
        exact ((hcx i).map (starRingEnd D.host.E).toIntAlgHom).mul (hdt' i)
      refine ⟨⟨_, hint⟩, ?_⟩
      change (∑ i, star ((c • x) i) * (d • t) i) = _
      simp only [t, Pi.smul_apply, nsmul_eq_mul, Nat.cast_mul, star_mul, star_natCast,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hm : (c * d) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have hn : (c * d : D.host.E) ≠ 0 := by
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc))
        (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd))
    have hm' : (c * d : D.host.E) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) := by
      simpa [Nat.cast_mul, ← Nat.cast_smul_eq_nsmul D.host.E] using hm
    have := Submodule.smul_mem (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))) (c * d : D.host.E)⁻¹ hm'
    simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using this
  exact exists_denom_stab D.sp.cm V.gram Λ (Submodule.IsLattice.fg D.host.E Λ)
    hsp

end GlobalTheory.LevelDenom

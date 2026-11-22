module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.PieriBlockIdeals.StatementLA
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExactExponentsSmulMemLocalizedCoeffLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
public import Formalism.LocalToGlobal.Divisibility.BrJoint
public import Formalism.LocalToGlobal.Columns.CoefficientsModP
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaFirst
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSmulMemOfLeLocP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeEmbeddedLastCoordinateSumStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjugateSubstLinearEquivSymmMemNablaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeOfLastCoordinateExtensionStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BrPairLocal

theorem finLocal : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) {n N : ℕ}
    (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n),
    (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) →
    ∀ (M : Submodule (𝓞 E) (Fin n → E)) (L : Submodule (𝓞 E) (Fin N → E)), Submodule.IsFullLattice E M →
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    u ∈ nabAtr emb Λ L → v ∈ nabAtr emb (fun τ => (σ τ).dual) M →
    GlobalTheory.BrPairF.brPairF σ hN Λ u v = 0 ∨
      -Formalism.DivisionValues.vw w (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Λ τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) ≤
        Formalism.DivisionValues.vw w (GlobalTheory.BrPairF.brPairF σ hN Λ u v) := by
  intro E K ι _ _ _ _ _ _ emb n N hN Λ σ hI hS M L hM hL w u v hu hv
  have hLlat : Submodule.IsFullLattice E L := by
    haveI : Submodule.IsLattice E L := GlobalTheory.T.isLattice_of_lastCoordinate_extension hN M L hM.toIsLattice hL
    refine ⟨?_⟩
    subst hN
    have hiC : ∀ k : Fin n, Formalism.L2.Col.Br.iC (rfl : n + 1 = n + 1) k = Fin.castSucc k := fun k => Fin.ext rfl
    have hiL : Formalism.L2.Col.Br.iL (rfl : n + 1 = n + 1) = Fin.last n := Fin.ext rfl
    simp only [hiC, hiL] at hL
    let g : (Fin n → E) →ₗ[E] (Fin (n + 1) → E) :=
      { toFun := fun x => Fin.snoc (α := fun _ => E) x 0
        map_add' := by intro x y; ext j; refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
        map_smul' := by intro a x; ext j; refine Fin.lastCases ?_ (fun i => ?_) j <;> simp }
    let e : Fin (n + 1) → E := Pi.single (Fin.last n) 1
    have gm : ∀ m ∈ M, g m ∈ L := fun m hm => (hL _).2 ⟨by simpa [g] using hm, 0, by simp [g]⟩
    have he : e ∈ L := (hL _).2 ⟨by
      have : (fun k : Fin n => e (Fin.castSucc k)) = 0 := by
        funext k; simp [e, Pi.single_apply, Fin.castSucc_ne_last]
      rw [this]; exact M.zero_mem, 1, by simp [e]⟩
    have hg : ∀ x : Fin n → E, g x ∈ Submodule.span E (L : Set (Fin (n + 1) → E)) := by
      intro x
      have hx : x ∈ Submodule.span E (M : Set (Fin n → E)) := by rw [hM.span_eq_top]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (gm x hx)
      | zero => simp
      | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
      | smul a x hx ih => simpa using Submodule.smul_mem _ a ih
    apply top_unique
    intro x _
    have dec : x = g (fun k => x (Fin.castSucc k)) + x (Fin.last n) • e := by
      ext j; refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [g, e, Pi.single_apply, Fin.castSucc_ne_last]
    rw [dec]
    exact Submodule.add_mem _ (hg _) (Submodule.smul_mem _ _ (Submodule.subset_span he))
  have h1 := GlobalTheory.OntoExponentsLat.exZ_sum_smul_mem_locP_delAtr E K ι N emb Λ L hLlat w u hu
  obtain ⟨s, hs, hsu⟩ := (Formalism.L2.DIV.lc_mem_locP w _ _).1 h1
  have hdel : delAtr emb Λ L = delK Λ (fun τ => Formalism.L2.Col.Br.sumLat hN (dualFr (tauLat emb τ M)) (1 : K)) := by
    unfold delAtr
    congr 1
    funext τ
    exact GlobalTheory.T.dualLattice_embedded_lastCoordinate_sum emb hN M L hL τ
  rw [hdel] at hsu
  have h2 := GlobalTheory.BranchFormula.integrality Formalism.L2.DIV.BrJ.branching_interlacing_pairs K ι N n hN Λ σ hI hS
    (fun τ => dualFr (tauLat emb τ M)) (fun _ => 1) (fun _ => one_ne_zero) _ hsu
  have hbr : Formalism.L2.Col.Br.brAt hN Λ σ (fun _ => (1 : K)) = Formalism.L2.Col.Br.brStd hN Λ σ := by
    simp [Formalism.L2.Col.Br.brAt]
  rw [hbr] at h2
  have hy := GlobalTheory.T.adjugateSubstLinearEquiv_symm_mem_nabla emb σ M hM.toIsLattice v hv
  have h3 := ((Formalism.L2.DIV.pairBDual E K ι n emb σ M hM _).1.1 h2) _ hy
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 h3
  have key : (s : K) * (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Λ τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) *
      GlobalTheory.BrPairF.brPairF σ hN Λ u v = (r : K) := by
    have e1 : (r : K) = algebraMap (𝓞 K) K r := rfl
    rw [e1, hr, GlobalTheory.BrPairF.brPairF_apply, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
      LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, LinearMap.smul_apply, LinearMap.smul_apply,
      Algebra.smul_def, Algebra.smul_def, map_pow, map_natCast, mul_assoc]
  by_cases hP : GlobalTheory.BrPairF.brPairF σ hN Λ u v = 0
  · exact Or.inl hP
  right
  have hs0 : (s : K) ≠ 0 := by
    intro h0
    apply hs
    have : s = 0 := by exact_mod_cast h0
    rw [this]
    exact w.asIdeal.zero_mem
  have hp0 : (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Λ τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Formalism.EigenvalueLevelCeiling.plc_prime w).ne_zero)
  have h4 := Formalism.DivisionValues.ReductionFirst.vw_int_nonneg w r
  rw [← key, Formalism.DivisionValues.ReductionFirst.vw_mul w (mul_ne_zero hs0 hp0) hP, Formalism.DivisionValues.ReductionFirst.vw_mul w hs0 hp0,
    Formalism.DivisionValues.ReductionFirst.vw_unit w s hs] at h4
  linarith

end GlobalTheory.BrPairLocal

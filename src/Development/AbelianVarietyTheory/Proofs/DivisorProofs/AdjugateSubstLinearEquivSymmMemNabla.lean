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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem funEquiv_symm_mem_nabAt_of_nabAtr : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι]
    (emb : ι → E →+* K) {n : ℕ} (σ : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsLattice E M → ∀ (v : VV K fun τ => (σ τ).dual),
    v ∈ nabAtr emb (fun τ => (σ τ).dual) M → (GlobalTheory.FunObj.funEquiv σ).symm v ∈ nabAt emb σ M := by
  intro E K ι _ _ _ _ _ emb n σ M hM v hv
  have hA : ∀ τ, (tauLat emb τ M).FG := by
    classical
    intro τ
    obtain ⟨S, hS⟩ := hM.fg
    rw [Formalism.L2.DIV.du_tauLat_eq, ← hS, Formalism.L2.DIV.du_tl_span]
    exact ⟨S.image (Formalism.L2.DIV.du_f (emb τ)), by rw [Finset.coe_image]⟩
  change ((GlobalTheory.FunObj.funEquiv σ).symm v).1 ∈ nabP σ (fun τ => tauLat emb τ M)
  simp only [nabP, transLat, Submodule.mem_iInf, Submodule.mem_comap]
  intro w B hB
  have hB' : ∀ τ, IsBasisAt w (dualFr (tauLat emb τ M)) (invTrK B τ) := fun τ =>
    GlobalTheory.DualWeylDual.isBasisAt_dualFr w (hA τ) (hB τ)
  have h1 : v.1 ∈ nabP (fun τ => (σ τ).dual) (fun τ => dualFr (tauLat emb τ M)) := hv
  simp only [nabP, transLat, Submodule.mem_iInf, Submodule.mem_comap] at h1
  have h2 := h1 w (invTrK B) hB'
  rw [← map_inv] at h2
  obtain ⟨s, hs, hsv⟩ := (Formalism.L2.DIV.lc_mem_locP w _ _).1 h2
  refine (Formalism.L2.DIV.lc_mem_locP w _ _).2 ⟨s, hs, ?_⟩
  set F := (GlobalTheory.FunObj.funEquiv σ).symm v with hF
  have e2 : GlobalTheory.FunObj.funEquiv σ (s • rhoK σ B⁻¹ F) = s • rhoK (fun τ => (σ τ).dual) (invTrK B⁻¹) v := by
    rw [LinearMapClass.map_smul_of_tower, GlobalTheory.FunObj.funEquiv_rhoK, hF, LinearEquiv.apply_symm_apply]
  have h3 : (s • rhoK σ B⁻¹ F).1 ∈ nabStd K σ := by
    rw [GlobalTheory.FunObj.funEquiv_mem_nabStd, e2]
    exact hsv
  exact h3

end GlobalTheory

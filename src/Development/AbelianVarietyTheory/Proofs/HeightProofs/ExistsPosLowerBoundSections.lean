module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveOpen
public import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfB
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FullTranscendenceDegree
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCuspRestrictComp
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NoCommonZeroOfReadings
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsCompactOfDefinite

@[expose] public section

noncomputable section

namespace GlobalTheory.BignessCompare

open Formalism.L2.Pj NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.IndefiniteRowSideFullHecke.FullTranscendenceDegree (CuspAt XP Generates ptNorm l2Norm FullTrdeg SmallForm ExistsNonzeroCuspFormOfWeightPair CurveModelAt CurveModelExists
  ptNorm_nonneg)

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} [Fintype κ]

theorem bdd_of_mem_holSub (X : κ → Data E r) (la : ∀ c, Wt (X c).Ψ r) {P : FDSec X} (hP : P ∈ holSub X la) :
    ∃ M : ℝ, ∀ p : FPt X, (X p.1).pnorm (la p.1) (P p.1) p.2 ≤ M := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    choose C hC using fun c => (hP c).1.2
    refine ⟨∑ c, |C c|, fun p => (hC p.1 p.2 p.2.2).trans ((le_abs_self _).trans ?_)⟩
    exact Finset.single_le_sum (f := fun c => |C c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  | zero => exact ⟨0, fun p => (pnorm_zero _ _ _).le⟩
  | add P Q _ _ hP hQ =>
    obtain ⟨a, ha⟩ := hP
    obtain ⟨b, hb⟩ := hQ
    exact ⟨a + b, fun p => (pnorm_add_le _ _ _ _ _).trans (add_le_add (ha p) (hb p))⟩
  | smul a P _ hP =>
    obtain ⟨b, hb⟩ := hP
    exact ⟨‖a‖ * b, fun p => (pnorm_smul _ _ a _ _).le.trans (mul_le_mul_of_nonneg_left (hb p) (norm_nonneg _))⟩

end Model

section Weights

variable {D : D7} {j : ℕ}

end Weights

section Record

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)

variable {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
  (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ Z, gF Z (X.inc u F) = 0) → F = 0)


end Record

section Inst

variable {D : D7} {T : Formalism.L2.Pj.Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  {ka wL wF : WeightFamilies.Wt D j}






end Inst

end GlobalTheory.BignessCompare

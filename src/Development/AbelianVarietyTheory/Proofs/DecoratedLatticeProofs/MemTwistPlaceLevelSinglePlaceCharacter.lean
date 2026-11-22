module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
public import Formalism.LocalToGlobal.IndefiniteReal.RealRec
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.LevGlue

theorem mem_levS_datY_single : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (PP : Formalism.L2.DIV.Pl D.host.E), PP ∈ Q → (∀ PP' ∈ Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ PP' ∈ Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → PP' = PP) → ∀ (κ : GA D V), κ ∈ GfC V → (∀ PP' : Formalism.L2.DIV.Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → Lev.finE V κ ∈ Formalism.L2.DIV.St β → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1) → (κ ∈ levS V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) ↔ Lev.finE V κ ∈ Formalism.L2.DIV.St β ∧ Formalism.L2.DIV.redFn β PP (Lev.finE V κ) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) ∧ (Lev.finE V κ ∈ Formalism.L2.DIV.St β → Lev.levChi V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) κ = (((ξ PP (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 (Formalism.L2.DIV.redFn β PP (Lev.finE V κ))))⁻¹ : ℂˣ) : ℂ)) := by
  intro D V β r t j hr Pg Q P χ ξ PP hPQ hPg hQ κ hκ hoff
  have hPgoff : Lev.finE V κ ∈ Formalism.L2.DIV.St β → ∀ PP' ∈ Pg, Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1 :=
    fun hSt PP' hP => hoff PP' (hPg PP' hP) hSt
  have hQoff : Lev.finE V κ ∈ Formalism.L2.DIV.St β → ∀ PP' ∈ Q, PP' ≠ PP → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1 :=
    fun hSt PP' hP hne => hoff PP' (fun e => hne (hQ PP' hP e)) hSt
  have hrt : Lev.finE V κ ∈ Formalism.L2.DIV.St β →
      Formalism.L2.DIV.rTup β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) (Lev.finE V κ) = 1 := by
    intro hSt
    funext PP'
    show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn β PP'.1 _) = 1
    rw [hPgoff hSt _ PP'.2]
    exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  refine ⟨⟨fun h => ?_, fun ⟨hSt, hP⟩ => ?_⟩, fun hSt => ?_⟩
  · have h' : κ ∈ Lev.levG V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) := h
    rw [Lev.levG, Lev.levA, Subgroup.mem_inf, Subgroup.mem_comap, Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev] at h'
    obtain ⟨_, ⟨_, hSt, _, hq⟩, _⟩ := h'
    exact ⟨hSt, hq PP hPQ⟩
  · show κ ∈ Lev.levG V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B)
    rw [Lev.levG, Lev.levA, Subgroup.mem_inf, Subgroup.mem_comap, Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev]
    refine ⟨hκ, ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hSt, ?_, ?_⟩, ?_⟩
    · intro PP' hP'
      rw [hPgoff hSt PP' hP']
      exact one_mem _
    · intro PP' hP'
      by_cases e : PP' = PP
      · rw [e]
        exact hP
      · rw [hQoff hSt PP' hP' e]
        exact one_mem _
    · rw [hrt hSt]
      exact one_mem _
  · simp only [Lev.levChi]
    congr 1
    simp only [Formalism.L2.DIV.levFn]
    rw [hrt hSt, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, one_mul]
    rw [Finset.prod_eq_one (fun PP' hP' => Finset.prod_eq_one fun c _ => by
      rw [hPgoff hSt PP' hP', Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]), one_mul]
    rw [Finset.prod_eq_single_of_mem (s := (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B).Q) PP hPQ fun PP' hP hne => by
      rw [hQoff hSt PP' hP hne, Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]]
    simp [Lev.datY]

end GlobalTheory.LevGlue

end

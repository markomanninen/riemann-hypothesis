module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S

namespace GlobalTheory.Core.Rk

def IdE {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : Prop := ∀ x : X.B.I.E, HEq (X.ιE x) x


open GlobalTheory.Mem GlobalTheory.Mem.Col2 in
def TrueE (D : D7) : Prop :=
  ∃ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)),
    D = I.rec7 l Z ∧ ∃ w : World I l Z, IdE w.S.X

theorem TrueE.trueD {D : D7} (h : TrueE D) : TrueD D :=
  let ⟨B, X, I, l, Z, e, w, _⟩ := h; ⟨B, X, I, l, Z, e, ⟨w⟩⟩


def HD (D : D7) (L C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  Formalism.BasicNotions.Ties D ∧ Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D ∧ Deg.HypL D L C' Cl Cg cb Cu cT CT ∧ Deg.DataNW D ∧ Formalism.L2.SG.RowsConc.TFrameAt D

def LedE (D : D7) (L C' : ℝ) : Prop := ∃ large₂ : SizeData₂ D, large₂.sc.L = L ∧ 8 * large₂.CGam ≤ C'

def GamLe (D : D7) (L C' : ℝ) : Prop := ∀ u : D.what₂.Word, 8 * Real.log (D.mem u).A.GamP ≤ C' * mfL D L

def Row (E : D7 → ℝ → ℝ → Prop) (Q : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C C'₀ Cl₀ : ℝ, 1 ≤ C ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : ℝ) (u : D.what₂.Word), TrueE D → E D L C' → HD D L C' Cl Cg cb Cu cT CT → Q D u L C

variable (E : D7 → ℝ → ℝ → Prop)

def RowDiag : Prop := Row E fun D u L C => SDiag D u L C

def RKRowAbs : Prop := Row E fun D u L C => RankMu D u → C * D.R.f * D.R.k * L ≤ Real.log (D.mem u).A.GamP → RK D u

def Inh (P : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop) : Prop :=
  ∃ Cg cb Cu cT CT : ℝ, 0 < cb ∧ 0 < cT ∧ ∀ C C'₀ Cl₀ : ℝ, ∃ (C' Cl L : ℝ) (D : D7), C'₀ ≤ C' ∧ Cl₀ ≤ Cl ∧
    TrueE D ∧ E D L C' ∧ HD D L C' Cl Cg cb Cu cT CT ∧ ∀ u, P D u L C

def InhAbs : Prop := Inh E fun D u L C => RankMu D u ∧ C * D.R.f * D.R.k * L ≤ Real.log (D.mem u).A.GamP

variable {E}

theorem Inh.reach {P Q : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop} (h : Inh E P) (h' : Row E fun D u L C => P D u L C → Q D u L C) :
    ∃ (D : D7) (L C : ℝ), TrueE D ∧ 1 ≤ C ∧ ∀ u, Q D u L C :=
  let ⟨Cg, cb, Cu, cT, CT, h1, h2, h⟩ := h
  let ⟨C, a, b, hC, h'⟩ := h' Cg cb Cu cT CT h1 h2
  let ⟨C', Cl, L, D, ha, hb, hD, he, hH, hP⟩ := h C a b
  ⟨D, L, C, hD, hC, fun u => h' C' Cl ha hb D L u hD he hH (hP u)⟩

theorem Inh.not_row_false {P : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop} (h : Inh E P) :
    ¬ Row E fun D u L C => P D u L C → False := fun h' =>
  let ⟨D, _, _, _, _, h⟩ := h.reach (Q := fun _ _ _ _ => False) h'
  h D.u₀

theorem one_le_mfL {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (hH : Deg.HypL D L C' Cl Cg cb Cu cT CT) :
    1 ≤ mfL D L ∧ 16 ≤ D.R.k ∧ 1 ≤ D.R.f := by
  obtain ⟨h1, -, h3, h4, -⟩ := hH
  have hm := D.R.two_le_m
  have h16 : 2 ^ 4 ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm 4
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by omega : 1 ≤ D.R.f)
  have hm' : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ D.R.m))
  refine ⟨?_, by omega, by omega⟩
  unfold mfL
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hm' hf) h1.le

theorem LedE.gamLe {D : D7} {L C' : ℝ} (h : LedE D L C') : GamLe D L C' := by
  obtain ⟨large₂, hL, h8⟩ := h
  intro u
  have hG := large₂.Gam_eq u
  have hL0 : 0 ≤ L := hL ▸ Real.rpow_nonneg (zero_le_one.trans large₂.sc.one_lt_alt.le) _
  rw [hL] at hG
  have hx : 0 ≤ mfL D L := by unfold mfL; positivity
  have e : Real.log (D.mem u).A.GamP = large₂.CGam * mfL D L := by rw [hG]; unfold mfL; ring
  rw [e]
  nlinarith

theorem GamLe.le_k {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (h : GamLe D L C') (hH : Deg.HypL D L C' Cl Cg cb Cu cT CT)
    (u : D.what₂.Word) : 8 * Real.log (D.mem u).A.GamP ≤ D.R.k := by
  refine (h u).trans (le_trans (le_of_eq ?_) hH.2.1)
  unfold mfL
  ring

theorem GamLe.log_lt {D : D7} {L C C' Cl Cg cb Cu cT CT : ℝ} (h : GamLe D L C') (hH : Deg.HypL D L C' Cl Cg cb Cu cT CT)
    (hC : 1 ≤ C) (u : D.what₂.Word) : Real.log (D.mem u).A.GamP < C * D.R.f * D.R.k * L := by
  have h1 := h.le_k hH u
  obtain ⟨-, hk, hf⟩ := one_le_mfL hH
  have hk' : (16 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have a : (1 : ℝ) ≤ C * D.R.f * L := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hf') hH.1.le
  nlinarith

theorem RKRowAbs.of_gamLe (hE : ∀ D L C', E D L C' → GamLe D L C') : RKRowAbs E :=
  fun _ _ _ _ _ _ _ => ⟨1, 0, 0, le_rfl, fun _ _ _ _ _ _ u _ he hH _ h =>
    absurd h (not_le.2 ((hE _ _ _ he).log_lt hH.2.2.1 le_rfl u))⟩

theorem not_inhAbs_of_gamLe (hE : ∀ D L C', E D L C' → GamLe D L C') : ¬ InhAbs E := fun h =>
  Inh.not_row_false h fun _ _ _ _ _ _ _ => ⟨1, 0, 0, le_rfl, fun _ _ _ _ _ _ u _ he hH h =>
    absurd h.2 (not_le.2 ((hE _ _ _ he).log_lt hH.2.2.1 le_rfl u))⟩

end GlobalTheory.Core.Rk

end
